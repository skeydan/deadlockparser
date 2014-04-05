
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
import Data.List
import Text.Printf
import Data.Time.Format
import System.Locale
import System.Exit
import Data.Time
import Data.Time.Calendar

main = do
  -- withArgs ["TSUN1_lmd0_31213.trc", "TSUN2_lmd0_31031.trc", "TSUN3_lmd0_30978.trc", "TSUN4_lmd0_31868.trc" ] main
  files     <- getArgs
  when (null files) (printf "\nusage: ./deadlockparser [file ..]\n\n" >> exitSuccess)
  currDir   <- getCurrentDirectory
  let encoding  = latin1
  let filepaths = map ((currDir ++ "/") ++) files
  -- not currently used, so save time
  -- resources <- liftM sequence (mapM (\p -> parseWithEncoding encoding parseResources p) filepaths)
  enqueues  <- liftM sequence (mapM (\p -> parseWithEncoding encoding parseEnqueues p) filepaths)
  wfgs      <- liftM sequence (mapM (\p -> parseWithEncoding encoding parseWFGS p) filepaths)
  deadlocks <- case wfgs of
    Left _   -> return Nothing
    Right ws -> case enqueues of
      Left _     -> return Nothing
      Right enqs -> return (Just (map (\w -> buildDeadlockMap w (join enqs)) (join ws)))
  case deadlocks of
    Nothing  -> print "Files could not be parsed"
    Just dls -> printDeadlocks $ sort dls

printDeadlocks :: [Deadlock] -> IO ()
printDeadlocks deadlocks = do
  printf "\n------------------------------------------\n***              Deadlocks             ***\n------------------------------------------"
  printf "\nFirst in tracefiles:   %s" (show $ datetime (minimum deadlocks))
  printf "\nLast in tracefiles:    %s" (show $ datetime (maximum deadlocks))
  printf "\nDeadlocks encountered: %d\n" (length deadlocks)
  mapM_ printDeadlock deadlocks

printDeadlock :: Deadlock -> IO ()
printDeadlock d = do
  printf "Deadlock at: %s\n--------------------------------\nBlockers:\n" (show $ datetime d)
  let blockers = M.findWithDefault []  BLOCKER (locksMap d)
  mapM_ printDeadlockItem blockers
  printf "Blocked:\n"
  let blocked = M.findWithDefault []  BLOCKED (locksMap d)
  mapM_ printDeadlockItem blocked
  printf "\n\n"

printDeadlockItem :: LockInfo -> IO ()
printDeadlockItem item =
  printf "  Address: %s    [Resource: %s-%s %s]\n    Session id: %s\n    User: %s\n    Machine: %s\n    SQL: %s\n"
  (addr item) (id1 (resourceId item)) (id2 (resourceId item)) (restype (resourceId item))
  (fromMaybe "[unknown]" (sessionId item)) (fromMaybe "[unknown]" (user item))
  (fromMaybe "[unknown]" (machine item)) (fromMaybe "[unknown]" (currentSQL item))

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

lookupLockInfo :: String -> [LockInfo] -> LockInfo
lookupLockInfo lockAddr (l:ls)
  | lockAddr == (addr l) = l
  | otherwise = lookupLockInfo lockAddr ls
lookupLockInfo lockAddr _ = LockInfo lockAddr Nothing Nothing Nothing Nothing (ResourceId "0x0" "0x0" "XX")


{- parsing section -}

parseWithEncoding :: TextEncoding -> Parser a -> FilePath -> IO (Either ParseError a)
parseWithEncoding encoding parser path = do
  h <- openFile path ReadMode
  hSetEncoding h latin1
  content <- hGetContents h
  return $ parse parser "" content

parseResources :: Parser [ResourceInfo]
parseResources = many1 (try (skipTillResource >> parseResource))

parseResource :: Parser ResourceInfo
parseResource = do
  addr         <- parseResAddr
  string "resname" >> many space >> char(':') >> many space
  resourceId   <- parseResName
  manyTill anyChar (try (string "Local inst") >> many space >> char(':') >> many space)
  instid       <- many1 digit
  manyTill anyChar (try (string "GRANTED_Q") >> many space >> char(':') >> many space)
  grantedQueue <- parseGrantedQueue <|> return []
  manyTill anyChar (try (string "CONVERT_Q") >> many space >> char(':') >> many space)
  convertQueue <- parseConvertQueue
  let resInfo  = ResourceInfo addr (read instid) resourceId grantedQueue convertQueue
  return resInfo
  --trace ("parseResource: " ++ show resInfo) return resInfo

skipTillResource :: Parser [Char]
skipTillResource = manyTill anyChar (try (lookAhead parseResAddr))

parseEnqueues :: Parser [LockInfo]
parseEnqueues = many1 (try (skipTillEnqueue >> parseEnqueue))

parseEnqueue :: Parser LockInfo
parseEnqueue = do
  addr    <- many1 hexDigit
  many1 space
  string "sid:" >> many space
  sid     <- many1 digit
  manyTill anyChar (try (string "O/S info: user:") >> many space)
  user    <- parseOracleIdentifier
  manyTill anyChar (try (string "machine:") >> many1 space)
  machine <- parseFQDN
  manyTill anyChar (try (string "current SQL:") >> many1 space)
  sql     <- manyTill anyChar (try (string "DUMP LOCAL BLOCKER"))
  let lockInfo = LockInfo addr (Just sid) (Just user) (Just machine) (Just sql) (ResourceId "0x0" "0x0" "XX")
  return $  lockInfo
  --trace ("parseEnqueue: " ++ show lockInfo) return $ lockInfo

skipTillEnqueue :: Parser [Char]
skipTillEnqueue = manyTill anyChar (try (string ("user session for deadlock lock 0x")))

parseWFGS :: Parser [WFG]
parseWFGS = many1 (try (skipTillWFG >> parseWFG))

parseWFG :: Parser WFG
parseWFG = do
  wfgs <- many1 parseWFGEntry
  skipMany1 (newline >> string "*** ")
  datetime <- parseDateTime
  return (datetime, wfgs)


skipTillWFG :: Parser [Char]
skipTillWFG = manyTill anyChar (try parseWFGMarker)

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

parseDateTime :: Parser LocalTime
parseDateTime = do
  datestring <- many1 (digit <|> oneOf ":- ")
  case (parseTime defaultTimeLocale "%F %T" datestring :: Maybe LocalTime) of
    Just datetime -> return datetime
    Nothing -> return $ LocalTime (ModifiedJulianDay 1) (TimeOfDay 0 0 0)

parseResAddr :: Parser [Char]
parseResAddr = do
  many1 (char '-') >> string "resource 0x"
  resaddr <- many1 hexDigit
  many1 (char '-') >> newline
  return resaddr

parseGrantedQueue :: Parser [QueueItem]
parseGrantedQueue = many parseGrantedQueueItem

parseConvertQueue :: Parser [QueueItem]
parseConvertQueue = many parseConvertQueueItem

parseGrantedQueueItem :: Parser QueueItem
parseGrantedQueueItem = do
  string "lp 0x"
  enqueueAddr <- many1 hexDigit
  string " gl "
  grantLevel  <- many1 upper
  manyTill anyChar (lookAhead (char '['))
  resname     <- parseResName
  return (QueueItem enqueueAddr grantLevel Nothing resname)

parseConvertQueueItem :: Parser QueueItem
parseConvertQueueItem = do
  string "lp 0x"
  enqueueAddr  <- many1 hexDigit
  string " gl "
  grantLevel   <- many1 upper
  string " rl "
  requestLevel <- many1 upper
  manyTill anyChar (lookAhead (char '['))
  resname      <- parseResName
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


{- types section -}

data Deadlock =  Deadlock {
  datetime  :: LocalTime,
  locksMap     :: M.Map Role [LockInfo]
} deriving (Eq, Ord)

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
  } deriving (Eq, Ord, Show, Read)

data ResourceInfo = ResourceInfo {
  resAddr     :: String,
  localInst   :: Int,
  name        :: ResourceId,
  grantedQueue:: Queue,
  convertQueue:: Queue
} deriving (Show, Read)
