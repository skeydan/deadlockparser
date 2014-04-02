
module Main (
    main
) where

import System.Environment
import System.Directory
import System.IO
import Text.ParserCombinators.Parsec
import Debug.Trace
import Numeric
import Data.Maybe
import Data.Char
import Control.Monad
import qualified Data.Map as M
import Text.Printf
import Data.Time.Format
import System.Locale
import Data.Time
import Data.Time.Calendar

main = do
  --files <- getArgs
  currDir <- getCurrentDirectory
  let encoding = latin1
  --let filepaths = map ((currDir ++ "/") ++)  ["munip1_lmd0_5702.trc", "munip2_lmd0_5966.trc"]
  --let filepaths = map ((currDir ++ "/") ++)  ["TSUN4_lmd0_31868.trc"]
  --let filepaths = map ((currDir ++ "/") ++)  ["TSUN3_lmd0_30978.trc"]
  let filepaths = map ((currDir ++ "/") ++)  ["TSUN2_lmd0_31031.trc"]
  --let filepaths = map ((currDir ++ "/") ++)  ["TSUN1_lmd0_31213.trc"]
  allres <- mapM (\p -> parseWithEncoding encoding parseResources p) filepaths
  allenqs <- mapM (\p -> parseWithEncoding encoding parseEnqueues p) filepaths
  allwfgs <- mapM (\p -> parseWithEncoding encoding parseWFGS p) filepaths
  let resources = sequence allres
  let enqueues = sequence allenqs
  let wfgs = sequence allwfgs
  deadlocks <- case wfgs of
    Left _ -> return Nothing
    Right ws -> case enqueues of
      Left _ -> return Nothing
      Right enqs -> return (Just (map (\w -> buildDeadlockMap w (join enqs)) (join ws)))
  case deadlocks of
    Nothing -> print "Files could not be parsed"
    Just dls -> printDeadlocks dls

printDeadlocks :: [Deadlock] -> IO ()
printDeadlocks deadlocks = do
  printf "---------\n* Deadlocks *\n-------\n\n"
  mapM_ printDeadlock deadlocks


printDeadlock :: Deadlock -> IO ()
printDeadlock d = do
  printf "Deadlock at: %s\n--------------------------------\nBlockers:\n" (show $ datetime d)
  let blockers = M.findWithDefault []  BLOCKER (locksMap d)
  mapM_ printDeadlockItem blockers
  printf "\nBlocked:\n"
  let blocked = M.findWithDefault []  BLOCKED (locksMap d)
  mapM_ printDeadlockItem blocked
  printf "\n\n"

printDeadlockItem :: LockInfo -> IO ()
printDeadlockItem item = do
  let lockaddr = addr item
  let resource = resourceId item
  case  (sessionId item) of
    Just sessid -> case (user item) of
      Just user -> case (machine item) of
        Just machine-> case (currentSQL item) of
          Just currentSQL -> printf
                               "  Address: %s\n    [Resource: %s-%s %s]    Session id: %s\n    User: %s\n    Machine: %s\n    SQL: %s\n"
                               lockaddr (id1 resource) (id2 resource) (restype resource) sessid user machine currentSQL
          Nothing -> printf "  Address: %s    [Resource: %s-%s %s] [Details unknown]\n" lockaddr (id1 resource) (id2 resource) (restype resource)
        Nothing -> printf "  Address: %s    [Resource: %s-%s %s] [Details unknown]\n" lockaddr (id1 resource) (id2 resource) (restype resource)
      Nothing -> printf "  Address: %s    [Resource: %s-%s %s][Details unknown]\n" lockaddr (id1 resource) (id2 resource) (restype resource)
    Nothing -> printf "  Address: %s    [Resource: %s-%s %s] [Details unknown]\n" lockaddr (id1 resource) (id2 resource) (restype resource)


parseWithEncoding :: TextEncoding -> Parser a -> FilePath -> IO (Either ParseError a)
parseWithEncoding encoding parser path = do
  h <- openFile path ReadMode
  hSetEncoding h latin1
  content <- hGetContents h
  return $ parse parser "" content


buildDeadlockMap ::  WFG -> [LockInfo] -> Deadlock
buildDeadlockMap (datetime, wfgentries) enqs =
  Deadlock
    datetime
    (foldr (\wfgentry m -> do
      let resourceForLock = resource wfgentry
          lockInfoForItem = lookupLockInfo (lockaddr wfgentry) enqs
      M.insertWith
         (++)
        (role wfgentry)
        ([lockInfoForItem { resourceId = resourceForLock }])
       m)
      M.empty
      wfgentries)
  --where bothRoles new old = old ++ new

lookupLockInfo :: String -> [LockInfo] -> LockInfo
lookupLockInfo lockAddr (l:ls)
  | lockAddr == (addr l) = l
  | otherwise = lookupLockInfo lockAddr ls
lookupLockInfo lockAddr _ = LockInfo lockAddr Nothing Nothing Nothing Nothing (ResourceId "0x0" "0x0" "XX")

parseResources :: Parser [ResourceInfo]
parseResources = do
  resources <- many1 (try (skipTillResource >> parseResource))
  return resources

parseResource :: Parser ResourceInfo
parseResource = do
  addr <- parseResAddr
  string "resname" >> many space >> char(':') >> many space
  resourceId <- parseResName
  manyTill anyChar (try (string "Local inst") >> many space >> char(':') >> many space)
  instid <- many1 digit
  manyTill anyChar (try (string "GRANTED_Q") >> many space >> char(':') >> many space)
  grantedQueue <- parseGrantedQueue <|> return []
  manyTill anyChar (try (string "CONVERT_Q") >> many space >> char(':') >> many space)
  convertQueue <- parseConvertQueue
  let resInfo = ResourceInfo addr (read instid) resourceId grantedQueue convertQueue
  return resInfo
  --trace ("parseResource: " ++ show resourceId) return resInfo

skipTillResource :: Parser [Char]
skipTillResource = do
  skip <- manyTill anyChar (try (lookAhead parseResAddr) )
  --trace ("skipTillResource: " ++ show skip) return skip
  return skip

parseEnqueues :: Parser [LockInfo]
parseEnqueues = do
  enqueues <- many1 (try (skipTillEnqueue >> parseEnqueue))
  return enqueues

parseEnqueue :: Parser LockInfo
parseEnqueue = do
  addr <- many1 hexDigit
  many1 space
  string "sid:" >> many space
  sid <- many1 digit
  manyTill anyChar (try (string "O/S info: user:") >> many space)
  user <- parseOracleIdentifier
  manyTill anyChar (try (string "machine:") >> many1 space)
  machine <- parseFQDN
  manyTill anyChar (try (string "current SQL:") >> many1 space)
  sql <- manyTill anyChar (try (string "DUMP LOCAL BLOCKER"))
  let lockInfo = LockInfo addr (Just sid) (Just user) (Just machine) (Just sql) (ResourceId "0x0" "0x0" "XX")
  return $  lockInfo
  --trace ("parseEnqueue: " ++ show sql) return $ lockInfo

skipTillEnqueue :: Parser [Char]
skipTillEnqueue = do
  skip <- manyTill anyChar (try (string ("user session for deadlock lock 0x")))
  --trace ("skipTillEnqueue: " ++ show skip) return skip
  return skip

parseWFGS :: Parser [WFG]
parseWFGS = do
  wfgs <- many1 (try (skipTillWFG >> parseWFG))
  return wfgs

parseWFG :: Parser WFG
parseWFG = do
  wfgs <- many1 parseWFGEntry
  skipMany1 (newline >> string "*** ")
  datetime <- parseDateTime
  return (datetime, wfgs)

parseDateTime :: Parser LocalTime
parseDateTime = do
  datestring <- many1 (digit <|> oneOf ":- ")
  case (parseTime defaultTimeLocale "%F %T" datestring :: Maybe LocalTime) of
    Just datetime -> return datetime
    Nothing -> return $ LocalTime (ModifiedJulianDay 1) (TimeOfDay 0 0 0)

skipTillWFG :: Parser [Char]
skipTillWFG = do
  skip <- manyTill anyChar (try parseWFGMarker)
  --trace ("skipTillWFG: " ++ show skip) return skip
  return skip

parseWFGMarker :: Parser [Char]
parseWFGMarker = do
  string "Global Wait-For-Graph(WFG) at ddTS["
  wfgLoc <- many1 (alphaNum <|> oneOf".")
  string "] :\n"
  --trace ("parseWFGMarker: " ++ wfgLoc) return wfgLoc
  return wfgLoc

parseWFGEntry :: Parser WFGEntry
parseWFGEntry = do
  role      <- try (string "BLOCKER") <|> string "BLOCKED"
  skipMany1 (space >> string "0x")
  lockaddr  <- many1 hexDigit
  skipMany1 (space >> (many1 digit) >> space >> string "wq" >> space >>
            (many1 digit) >> space >> string "cvtops" >> space >>
            char 'x' >> (many1 digit) >> space)
  restype   <- manyTill upper space
  skipMany1 (string "0x")
  id1       <- liftM ("0x" ++) $ manyTill hexDigit (string ".0x")
  id2       <- liftM ("0x" ++) $ manyTill hexDigit (string "(ext ")
  manyTill (hexDigit <|> oneOf ")[]x,-") (string " inst ")
  instid    <- manyTill digit (space >> newline)
  let wfgEntry = WFGEntry (read role :: Role)
                          lockaddr
                          (ResourceId id1 id2 restype)
                          (read instid)
  --trace ("parseWFGEntry: " ++ show wfgEntry) return $ wfgEntry
  return $ wfgEntry

parseResAddr :: Parser [Char]
parseResAddr = do
  many1 (char '-') >> string "resource 0x"
  resaddr <- many1 hexDigit
  many1 (char '-') >> newline
  return resaddr
{-
parseLockAddr :: Parser [Char]
parseLockAddr = do
  many1 (char '-') >> string "enqueue 0x"
  lockaddr <- many1 hexDigit
  many1 (char '-') >> newline
  --trace ("parseLockAddr: " ++ show lockaddr) return lockaddr
  return lockaddr
-}
parseGrantedQueue :: Parser [QueueItem]
parseGrantedQueue = many parseGrantedQueueItem

parseConvertQueue :: Parser [QueueItem]
parseConvertQueue = many parseConvertQueueItem

parseGrantedQueueItem :: Parser QueueItem
parseGrantedQueueItem = do
  string "lp 0x"
  enqueueAddr <- many1 hexDigit
  string " gl "
  grantLevel <- many1 upper
  manyTill anyChar (lookAhead (char '['))
  resname <- parseResName
  return (QueueItem enqueueAddr grantLevel Nothing resname)

parseConvertQueueItem :: Parser QueueItem
parseConvertQueueItem = do
  string "lp 0x"
  enqueueAddr <- many1 hexDigit
  string " gl "
  grantLevel <- many1 upper
  string " rl "
  requestLevel <- many1 upper
  manyTill anyChar (lookAhead (char '['))
  resname <- parseResName
  return (QueueItem enqueueAddr grantLevel (Just requestLevel) resname)

parseResName :: Parser ResourceId
parseResName = do
  string "[0x"
  id1 <- liftM ("0x" ++) $ many1 hexDigit
  string "][0x"
  id2 <- liftM ("0x" ++) $ many1 hexDigit
  string "],["
  restype   <- manyTill upper (char ']')
  return (ResourceId id1 id2 restype)
  --trace (show (ResourceId id1 id2 restype)) return (ResourceId id1 id2 restype)

parseOracleIdentifier :: Parser [Char]
parseOracleIdentifier = many1 (alphaNum <|> oneOf"$#_")

parseFQDN :: Parser [Char]
parseFQDN = many1 (alphaNum <|> oneOf ".-")

parseTillEOF :: Parser [Char]
parseTillEOF = do
  anyCs <- many1 anyChar
  eof
  --trace ("parseTillEOF: " ++ anyCs) return anyCs
  return anyCs

data Deadlock =  Deadlock {
  datetime  :: LocalTime,
  locksMap     :: M.Map Role [LockInfo]
}

data ResourceId = ResourceId {
  id1       :: String,
  id2       :: String,
  restype   :: String
} deriving (Eq, Show, Read, Ord)

data WFGEntry = WFGEntry {
  role      :: Role,
  lockaddr  :: String,
  resource  :: ResourceId,
  instid    :: Int
} deriving (Show, Read)

type WFG = (LocalTime, [WFGEntry])

data Role = BLOCKED | BLOCKER deriving (Eq, Ord, Show, Read)

type LockAddr = String

data QueueItem = QueueItem {
  enqueueAddr   :: LockAddr,
  grantLevel    :: String,
  requestLevel  :: Maybe String,
  resname       :: ResourceId
} deriving (Show, Read)

type Queue = [QueueItem]

data LockInfo = LockInfo {
  addr        :: String,
  sessionId   :: Maybe String,
  user        :: Maybe String,
  machine     :: Maybe String,
  currentSQL  :: Maybe String,
  resourceId  :: ResourceId
  } deriving (Show, Read)

data ResourceInfo = ResourceInfo {
  resAddr     :: String,
  localInst   :: Int,
  name        :: ResourceId,
  grantedQueue:: Queue,
  convertQueue:: Queue
} deriving (Show, Read)
