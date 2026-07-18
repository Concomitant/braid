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
  { rsEnv      :: Env        -- prims + user defs
  , rsRun      :: RunDefs    -- runtime bodies of user defs
  , rsUserDefs :: [String]   -- user def names, in definition order
  , rsStackTy  :: SType      -- type of the current stack (internal names)
  , rsStack    :: [Value]    -- the current stack, front wire first
  }

initialState :: ReplState
initialState = ReplState primEnv M.empty [] SEnd []

repl :: IO ()
repl = do
  hSetBuffering stdout NoBuffering
  putStrLn "Braid REPL — each line runs against the current stack."
  putStrLn "Commands: :t <prog> type, :s stack, :defs, :clear, :q quit"
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
          case rsUserDefs st of
            [] -> putStrLn "no definitions"
            ns -> mapM_ (putStrLn . renderDef st) ns
          loop st
        l | ":t " `isPrefixOf` l -> do
              typeOf st (drop 3 l)
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
    Just sc -> "def " ++ name ++ " : " ++ show sc
    Nothing -> "def " ++ name ++ " : ???"

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
    Right ([(name, _)], rest)
      | all isSpace rest -> defLine name
    Right ([], _) -> programLine
    Right _       -> report "one definition per line, please"
  where
    report err = putStrLn ("error: " ++ err) >> pure st

    -- def name = program : extend (or replace) a user definition
    defLine name = do
      let envBase
            | name `elem` rsUserDefs st = M.delete name (rsEnv st)
            | otherwise                 = rsEnv st
      case checkModuleWith envBase line of
        Left err -> report err
        Right m  ->
          case modDefs m of
            [(n, sc, _)] -> do
              putStrLn $ "def " ++ n ++ " : " ++ show sc
              pure st
                { rsEnv      = modEnv m
                , rsRun      = moduleRunDefs m `M.union` rsRun st
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
  let (tvs, svs) = varsOfStack sty
      tm = M.fromList
             (zip tvs [ TVarTy (TV ("_a" ++ show n)) | n <- [0 :: Int ..] ])
      sm = M.fromList
             (zip svs [ STail (SV ("_r" ++ show n)) | n <- [0 :: Int ..] ])
      Arrow sty' _ = substOnce (Subst tm sm) (Arrow sty SEnd)
  in sty'
