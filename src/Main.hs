
module Main where

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

main = getArgs >>= handleArgs >>= showDeadlocks

handleArgs :: [String] -> IO (TextEncoding, [String])
handleArgs ["-h"] = usage >> exitSuccess
handleArgs []     = usage >> exitSuccess
handleArgs ("-e" : enc : files) =  do
    encoding <- mkTextEncoding enc
    return (encoding, files)
handleArgs files  = return (localeEncoding, files)

showDeadlocks :: (TextEncoding, [String]) -> IO ()
showDeadlocks (encoding, files) = do
  currDir   <- getCurrentDirectory
  let filepaths = map ((currDir ++ "/") ++) files
  -- not currently used, so save time
  -- resources <- liftM sequence (mapM (\p -> parseWithEncoding encoding parseResources p) filepaths)
  enqueues  <- liftM sequence (mapM (\p -> parseWithEncoding encoding parseEnqueues p) filepaths)
  wfgs      <- liftM sequence (mapM (\p -> parseWithEncoding encoding parseWFGS p) filepaths)
  deadlocks <- case wfgs of
    Left e   -> fail ("Could not parse wait-for-graphs:" ++ show e)
    Right ws -> case enqueues of
      Left e     -> fail ("Could not parse enqueues:" ++ show e)
      Right enqs -> return (Just (map (\w -> buildDeadlockMap w (join enqs)) (join ws)))
  case deadlocks of
    Nothing  -> fail "Error building up deadlock map"
    Just dls -> printDeadlocks $ sort dls

usage :: IO a
usage = (printf "\nusage: ./deadlockparser [-e encoding] file1 file2 ... file<n>\n\n"
        >> exitSuccess)

printDeadlocks :: [Deadlock] -> IO ()
printDeadlocks deadlocks = do
  printf "\n------------------------------------------\n"
  printf "***              Deadlocks             ***\n"
  printf "------------------------------------------"
  printf "\nFirst in tracefiles:   %s" (show $ datetime (minimum deadlocks))
  printf "\nLast in tracefiles:    %s" (show $ datetime (maximum deadlocks))
  printf "\nDeadlocks encountered: %d\n------------------------------------------\n\n"
         (length deadlocks)
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
  printf "  Address: %s    [Resource: %s-%s %s]\n  Session id: %s\n  User: %s\n\
            \  Machine: %s\n  Current SQL: %s\n"
  (addr item) (id1 (resourceId item)) (id2 (resourceId item)) (restype (resourceId item))
  (fromMaybe "[unknown]" (sessionId item)) (fromMaybe "[unknown]" (user item))
  (fromMaybe "[unknown]" (machine item)) (fromMaybe "[unknown]\n" (currentSQL item))

buildDeadlockMap ::  WFG -> [LockInfo] -> Deadlock
buildDeadlockMap (datetime, wfgentries) enqs =
  Deadlock
    datetime
    (foldr (\wfgentry m -> do
      let lockInfoForItem = lookupLockInfo (lockaddr wfgentry) (resource wfgentry) enqs
      M.insertWith
         (++)
        (role wfgentry)
        ([lockInfoForItem])
       m)
      M.empty
      wfgentries)

lookupLockInfo :: String -> ResourceId -> [LockInfo] -> LockInfo
lookupLockInfo lockAddr resAddr (l:ls)
  | lockAddr == (addr l) &&  resAddr == (resourceId l) = l
  | otherwise = lookupLockInfo lockAddr resAddr ls
lookupLockInfo lockAddr resAddr _ = LockInfo lockAddr Nothing Nothing Nothing Nothing resAddr

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
   <?> "resource information [parseResource]"

skipTillResource :: Parser [Char]
skipTillResource = manyTill anyChar (try (lookAhead parseResAddr))
                   <?> "anything preceding a resource address [skipTillResource]"

parseEnqueues :: Parser [LockInfo]
parseEnqueues = many1 (try (skipTillEnqueue >> parseEnqueue))
                <?> "lock information [parseEnqueues]"

parseEnqueue :: Parser LockInfo
parseEnqueue = do
  addr     <- many1 hexDigit
  many1 space
  string "sid:" >> many space
  sid      <- many1 digit
  many1 space >> string "ser:" >> many space
  ser      <- many1 digit
  manyTill anyChar (try (string "user:") >> many space)
  userId   <- many1 digit
  char '/'
  userName <- parseOracleIdentifier
  manyTill anyChar (try (string "machine:") >> many1 space)
  machine  <- parseFQDN
  manyTill anyChar (try (string "current SQL:") >> many1 space)
  sql      <- manyTill anyChar (try (string "DUMP LOCAL BLOCKER"))
  manyTill anyChar (try ((string "possible owner[") >> many1 digit >> char '.'
                          >> many1 digit >> string "] on resource "))
  resId    <- parseResNameEnqFmt
  let lockInfo = LockInfo addr (Just sid) (Just userName) (Just machine) (Just sql) resId
  return $  lockInfo
  --trace ("parseEnqueue: " ++ show lockInfo) return $ lockInfo
  <?> "lock information [parseEnqueue]"


skipTillEnqueue :: Parser [Char]
skipTillEnqueue = manyTill anyChar (try (string ("user session for deadlock lock 0x")))
                  <?> "anything preceding: user session for deadlock lock 0x [skipTillResource]"

parseWFGS :: Parser [WFG]
parseWFGS = many (try (skipTillWFG >> parseWFG))
            <?> "wait-for-graphs [parseWFGS]"

parseWFG :: Parser WFG
parseWFG = do
  wfgs <- many1 parseWFGEntry
  skipMany1 (newline >> string "*** ")
  datetime <- parseDateTime
  return (datetime, wfgs)
  <?> "wait-for-graph [parseWFG]"

skipTillWFG :: Parser [Char]
skipTillWFG = manyTill anyChar (try parseWFGMarker)
              <?> "anything preceding: Global Wait-For-Graph(WFG) at ddTS[ [skipTillWFG]"

parseWFGMarker :: Parser [Char]
parseWFGMarker = do
  string "Global Wait-For-Graph(WFG) at ddTS["
  wfgLoc <- many1 (alphaNum <|> oneOf".")
  string "] :\n"
  --trace ("parseWFGMarker: " ++ wfgLoc) return wfgLoc
  return wfgLoc
  <?> "sth like Global Wait-For-Graph(WFG) at ddTS[0.4496] :\\n [parseWFGMarker]"

parseWFGEntry :: Parser WFGEntry
parseWFGEntry = do
  role      <- try (string "BLOCKER") <|> string "BLOCKED"
  skipMany1 (space >> string "0x")
  lockaddr  <- many1 hexDigit
  skipMany1 (space >> (many1 digit) >> space >> string "wq" >> space >>
            (many1 digit) >> space >> string "cvtops" >> space >>
            char 'x' >> (many1 digit) >> space)
  resId     <- parseResNameWFGFmt
  string "(ext "
  manyTill (hexDigit <|> oneOf ")[]x,-") (string " inst ")
  instid    <- manyTill digit (space >> newline)
  let wfgEntry = WFGEntry (read role :: Role)
                          lockaddr
                          resId
                          (read instid)
  --trace ("parseWFGEntry: " ++ show wfgEntry) return $ wfgEntry
  return wfgEntry
   <?> "sth like BLOCKER 0x75e76e408 5 wq 2 cvtops x1 TX 0x7f0001.0x5fac(ext 0x39,0x0)\
                 \ [C7000-0001-00000007] inst 1 [parseWFGEntry]"

parseDateTime :: Parser LocalTime
parseDateTime = do
  datestring <- many1 (digit <|> oneOf ":- ")
  case (parseTime defaultTimeLocale "%F %T" datestring :: Maybe LocalTime) of
    Just datetime -> return datetime
    Nothing -> return $ LocalTime (ModifiedJulianDay 1) (TimeOfDay 0 0 0)
    <?> "sth like 2014-03-10 12:16:22.513 [parseDateTime]"

parseResAddr :: Parser [Char]
parseResAddr = do
  many1 (char '-') >> string "resource 0x"
  resaddr <- many1 hexDigit
  many1 (char '-') >> newline
  return resaddr
  <?> "sth like resource 0x75df152d8----------------------\\n [parseResAddr]"

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
  <?> "sth like lp 0x75e4fdcf8 gl KJUSERCW rp 0x749dc8a40 [0x661c1][0x0],[TM]\
       \ [parseGrantedQueueItem]"

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
  <?> "sth like lp 0x75e4f9230 gl KJUSERNL rl KJUSEREX rp 0x749faff18 [0x440008][0x279f0],[TX]\
      \ [parseConvertQueueItem]"


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
  <?> "sth like [0x7f0001][0x5fac],[TX] [parseResName]"

parseResNameEnqFmt :: Parser ResourceId
parseResNameEnqFmt = do
  restype   <- manyTill upper (char '-')
  id1 <- liftM (("0x" ++) . (map toLower) . dropWhile (== '0')) $ many1 hexDigit
  char '-'
  --id2_ <- many1 hexDigit
  --let id2 = ("0x" ++) . map toLower . (\x -> dropWhile (== '0') (init x) ++ [last x]) $ id2_
  id2 <- liftM (("0x" ++) . map toLower . (\x -> dropWhile (== '0') (init x) ++ [last x])) $ many1 hexDigit
  return (ResourceId id1 id2 restype)
  --trace (show (ResourceId id1 id2 restype)) return (ResourceId id1 id2 restype)
  <?> "sth like TX-007F0001-00005FAC [parseResNameEnqFmt]"

parseResNameWFGFmt :: Parser ResourceId
parseResNameWFGFmt = do
  restype   <- manyTill upper space
  skipMany1 (string "0x")
  id1       <- liftM ("0x" ++) $ manyTill hexDigit (string ".0x")
  id2       <- liftM ("0x" ++) $ many1 hexDigit
  return (ResourceId id1 id2 restype)
  --trace (show (ResourceId id1 id2 restype)) return (ResourceId id1 id2 restype)
  <?> "sth like TX 0x7f0001.0x5fac [parseResNameWFGFmt]"

parseOracleIdentifier :: Parser [Char]
parseOracleIdentifier = many1 (alphaNum <|> oneOf"$#_")
                        <?> "sth like theuser$ [parseOracleIdentifier]"

parseFQDN :: Parser [Char]
parseFQDN = many1 (alphaNum <|> oneOf ".-")
            <?> "sth like host.my-domain.com [N]"

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
