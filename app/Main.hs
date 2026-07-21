module Main (main) where

import MiniConcatTypechecker
import qualified Data.Map as M
import Data.Char (isSpace)
import Data.List (isPrefixOf)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO

main :: IO ()
main = do
  args <- getArgs
  case args of
    []     -> repl
    [path] -> runFile path
    _      -> do
      hPutStrLn stderr "usage: braid [file]"
      exitFailure

--------------------------------------------------------------------------------
-- Batch mode: typecheck and run a file
--------------------------------------------------------------------------------

runFile :: FilePath -> IO ()
runFile path = do
  src <- readFile path
  case runModule src of
    Left err -> do
      hPutStrLn stderr $ "error: " ++ err
      exitFailure
    Right (stack, logs) -> do
      mapM_ putStrLn logs
      case stack of
        [] -> pure ()
        _  -> putStrLn $ "stack: " ++ unwords (map show stack)

--------------------------------------------------------------------------------
-- REPL: a persistent value stack; each line is a program applied to it
--------------------------------------------------------------------------------

data ReplState = ReplState
  { rsEnv      :: Env        -- prims + prelude + user defs
  , rsRun      :: RunDefs    -- runtime bodies of prelude + user defs
  , rsDocs     :: M.Map String String   -- ## docs, prelude + user
  , rsUserDefs :: [String]   -- user def names, in definition order
  , rsStackTy  :: SType      -- type of the current stack (internal names)
  , rsStack    :: [Value]    -- the current stack, front wire first
  }

initialState :: ReplState
initialState =
  ReplState (modEnv preludeModule)
            (moduleRunDefs preludeModule)
            (modDocs preludeModule)
            [] SEnd []

repl :: IO ()
repl = do
  hSetBuffering stdout NoBuffering
  putStrLn "Braid REPL — each line runs against the current stack."
  putStrLn "Commands: :t <prog> type, :doc <name>, :s stack, :defs, :clear, :q quit"
  loop initialState

loop :: ReplState -> IO ()
loop st = do
  putStr "braid> "
  eof <- isEOF
  if eof
    then putStrLn ""
    else do
      line <- getLine
      case trim line of
        ""      -> loop st
        ":q"    -> pure ()
        ":quit" -> pure ()
        ":clear" -> do
          putStrLn "stack cleared"
          loop st { rsStackTy = SEnd, rsStack = [] }
        ":s" -> do
          putStrLn (renderStack st)
          loop st
        ":defs" -> do
          let preludeOnly = filter (`notElem` rsUserDefs st) preludeNames
          mapM_ (putStrLn . renderDef st) preludeOnly
          mapM_ (putStrLn . renderDef st) (rsUserDefs st)
          loop st
        l | ":t " `isPrefixOf` l -> do
              typeOf st (drop 3 l)
              loop st
          | ":doc " `isPrefixOf` l -> do
              docOf st (trim (drop 5 l))
              loop st
          | ":" `isPrefixOf` l -> do
              putStrLn $ "unknown command: " ++ l
              loop st
          | otherwise -> handleLine st l >>= loop

trim :: String -> String
trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

renderDef :: ReplState -> String -> String
renderDef st name =
  case M.lookup name (rsEnv st) of
    Just sc -> "def " ++ name ++ " : " ++ show sc ++ docSuffix
    Nothing -> "def " ++ name ++ " : ???"
  where
    docSuffix =
      case M.lookup name (rsDocs st) of
        Just d  -> "\n  ## " ++ d
        Nothing -> ""

docOf :: ReplState -> String -> IO ()
docOf st name
  | M.member name (rsEnv st) =
      case M.lookup name (rsDocs st) of
        Just d  -> putStrLn ("## " ++ d) >> putStrLn (renderTypeLine)
        Nothing -> putStrLn "(no doc)" >> putStrLn (renderTypeLine)
  | otherwise = putStrLn $ "unknown name: " ++ name
  where
    renderTypeLine =
      case M.lookup name (rsEnv st) of
        Just sc -> name ++ " : " ++ show sc
        Nothing -> name


renderStack :: ReplState -> String
renderStack st =
  case rsStack st of
    [] -> "stack: •"
    vs -> "stack: " ++ unwords (map show vs) ++ "  :  " ++ displayTy
  where
    -- pretty display names (a0/ρ0) without touching internal state
    displayTy =
      let Arrow _ o = normalizeArrow (Arrow SEnd (rsStackTy st))
      in show o

typeOf :: ReplState -> String -> IO ()
typeOf st src =
  case parseProgram src >>= inferTermIn (rsEnv st) of
    Left err  -> putStrLn $ "error: " ++ err
    Right arr -> putStrLn $ trim src ++ " : " ++ show (normalizeArrow arr)

handleLine :: ReplState -> String -> IO ReplState
handleLine st line =
  case splitDefs line of
    Left err -> report err
    Right ([(name, _, _)], rest)
      | all isSpace rest -> defLine name
    Right ([], _) -> programLine
    Right _       -> report "one definition per line, please"
  where
    report err = putStrLn ("error: " ++ err) >> pure st

    -- def name = program : extend (or replace) a user definition;
    -- prelude names may always be shadowed
    defLine name = do
      let envBase
            | name `elem` rsUserDefs st = M.delete name (rsEnv st)
            | otherwise                 = rsEnv st
      case checkModuleWith envBase preludeNames line of
        Left err -> report err
        Right m  ->
          case modDefs m of
            [(n, sc, _)] -> do
              putStrLn $ "def " ++ n ++ " : " ++ show sc
              pure st
                { rsEnv      = modEnv m
                , rsRun      = moduleRunDefs m `M.union` rsRun st
                , rsDocs     = modDocs m `M.union` rsDocs st
                , rsUserDefs =
                    rsUserDefs st ++ [n | n `notElem` rsUserDefs st]
                }
            _ -> report "internal: expected exactly one definition"

    -- a program line: typecheck against the current stack, then run
    programLine =
      case checkLine of
        Left err -> report err
        Right newTy ->
          case evalLine of
            Left err -> report ("runtime error: " ++ err)
            Right (stack', logs) -> do
              mapM_ putStrLn logs
              let st' = st { rsStackTy = freshenStackTy newTy
                           , rsStack   = stack' }
              putStrLn (renderStack st')
              pure st'

    checkLine = do
      term <- parseProgram line
      Arrow i o <- inferTermIn (rsEnv st) term
      s <- solve [CEqStack i (rsStackTy st)]
      pure (apply s o)

    evalLine = do
      term <- parseProgram line
      evalTerm (rsEnv st) (rsRun st) M.empty term (rsStack st)

-- Rename the stack type's free variables into a namespace the inference
-- fresh-name generator (a0…, ρ0…) can never produce, so vars surviving
-- across REPL lines (empty lists, quotations) don't collide with the
-- next line's fresh vars.
freshenStackTy :: SType -> SType
freshenStackTy sty =
  let (tvs, svs, rvs) = varsOfStack sty
      tm = M.fromList
             (zip tvs [ TVarTy (TV ("_a" ++ show n)) | n <- [0 :: Int ..] ])
      sm = M.fromList
             (zip svs [ STail (SV ("_r" ++ show n)) | n <- [0 :: Int ..] ])
      rm = M.fromList
             (zip rvs [ RTail (RV ("_s" ++ show n)) | n <- [0 :: Int ..] ])
      Arrow sty' _ = substOnce (Subst tm sm rm) (Arrow sty SEnd)
  in sty'
