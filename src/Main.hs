
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
  printf "\nDeadlocks\n---------\n\n"
  mapM_ printDeadlock deadlocks


printDeadlock :: Deadlock -> IO ()
printDeadlock d = do
  let resources = M.keys d
  printf "Deadlocks\n---------\n\nParticipants (resources): "
  mapM_ printDeadlockResource resources
  printf "\n"
  printDeadlockInfo d
  printf "\n"

printDeadlockInfo :: Deadlock -> IO ()
printDeadlockInfo = undefined


printDeadlockResource :: ResourceId -> IO ()
printDeadlockResource resource =
  printf "%s-%s %s  " (id1 resource) (id2 resource) (restype resource)


parseWithEncoding :: TextEncoding -> Parser a -> FilePath -> IO (Either ParseError a)
parseWithEncoding encoding parser path = do
  h <- openFile path ReadMode
  hSetEncoding h latin1
  content <- hGetContents h
  return $ parse parser "" content


buildDeadlockMap ::  WFG -> [LockInfo] -> Deadlock
buildDeadlockMap wfgs enqs =
  foldr (\wfgentry m ->
    M.insertWith
       bothRoles
      (resource wfgentry)
      ([LockInfoByRole (role wfgentry) (lookupLockInfo (lockaddr wfgentry) enqs)])
     m)
    M.empty
    wfgs
  where bothRoles new old = old ++ new

lookupLockInfo :: String -> [LockInfo] -> Maybe LockInfo
lookupLockInfo lockAddr (l:ls)
  | lockAddr == (addr l) = Just l
  | otherwise = lookupLockInfo lockAddr ls
lookupLockInfo addr _ = Nothing

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
  let lockInfo = LockInfo addr sid user machine sql
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
parseWFG = many1 parseWFGEntry

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
parseFQDN = many1 (alphaNum <|> oneOf ".")

parseTillEOF :: Parser [Char]
parseTillEOF = do
  anyCs <- many1 anyChar
  eof
  --trace ("parseTillEOF: " ++ anyCs) return anyCs
  return anyCs

type Deadlock =  M.Map ResourceId [LockInfoByRole]

data LockInfoByRole = LockInfoByRole {
  lockRole :: Role,
  maybeLockInfo :: Maybe LockInfo
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

type WFG = [WFGEntry]

data Role = BLOCKED | BLOCKER deriving (Eq, Ord, Show, Read)

data QueueItem = QueueItem {
  enqueueAddr   :: String,
  grantLevel    :: String,
  requestLevel  :: Maybe String,
  resname       :: ResourceId
} deriving (Show, Read)

type Queue = [QueueItem]

data LockInfo = LockInfo {
  addr        :: String,
  sessionId   :: String,
  user        :: String,
  machine     :: String,
  currentSQL  :: String
  } deriving (Show, Read)

data ResourceInfo = ResourceInfo {
  resAddr     :: String,
  localInst   :: Int,
  name        :: ResourceId,
  grantedQueue:: Queue,
  convertQueue:: Queue
} deriving (Show, Read)
