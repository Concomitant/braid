module Main (main) where

import MiniConcatTypechecker
import qualified Data.Map as M
import Data.Char (isSpace)
import Data.List (isPrefixOf, intercalate)
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
  , rsAliases  :: [Alias]    -- type aliases, match order (user first)
  , rsDatas    :: [DataDecl] -- recursive (nominal) type declarations
  , rsDocs     :: M.Map String String   -- ## docs, prelude + user
  , rsUserDefs :: [String]   -- user def names, in definition order
  , rsStackTy  :: SType      -- type of the current stack (internal names)
  , rsStack    :: [Value]    -- the current stack, front wire first
  }

initialState :: ReplState
initialState =
  ReplState (modEnv preludeModule)
            (moduleRunDefs preludeModule)
            (modAliases preludeModule)
            (modDatas preludeModule)
            (modDocs preludeModule)
            [] SEnd []

repl :: IO ()
repl = do
  hSetBuffering stdout NoBuffering
  putStrLn "Braid REPL — each line runs against the current stack."
  putStrLn "Commands: :t <prog> type (:t! raw), :doc <name>, :s stack, :defs, :clear, :q quit"
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
          mapM_ (putStrLn . renderData st) (reverse (rsDatas st))
          mapM_ (putStrLn . renderAlias st) (reverse (rsAliases st))
          let preludeOnly = filter (`notElem` rsUserDefs st) preludeNames
          mapM_ (putStrLn . renderDef st) preludeOnly
          mapM_ (putStrLn . renderDef st) (rsUserDefs st)
          loop st
        l | ":t! " `isPrefixOf` l -> do
              typeOfWith show st (drop 4 l)
              loop st
          | ":t " `isPrefixOf` l -> do
              typeOfWith (showArrowA (rsAliases st)) st (drop 3 l)
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

renderData :: ReplState -> DataDecl -> String
renderData st d =
  "type " ++ dName d ++ params ++ " = " ++ showTyA [] (dBody d) ++ docSuffix
  where
    params
      | null (dParams d) = ""
      | otherwise =
          "(" ++ intercalate ", " (map show (dParams d)) ++ ")"
    docSuffix =
      case M.lookup (dName d) (rsDocs st) of
        Just doc -> "\n  ## " ++ doc
        Nothing  -> ""

renderAlias :: ReplState -> Alias -> String
renderAlias st al =
  "type " ++ aName al ++ params ++ " = " ++ showTyA [] (aBody al) ++ docSuffix
  where
    params
      | null (aParams al) = ""
      | otherwise =
          "(" ++ intercalate ", " (map show (aParams al)) ++ ")"
    docSuffix =
      case M.lookup (aName al) (rsDocs st) of
        Just d  -> "\n  ## " ++ d
        Nothing -> ""

renderDef :: ReplState -> String -> String
renderDef st name =
  case M.lookup name (rsEnv st) of
    Just sc -> "def " ++ name ++ " : " ++ showSchemeA (rsAliases st) sc
                 ++ docSuffix
    Nothing -> "def " ++ name ++ " : ???"
  where
    docSuffix =
      case M.lookup name (rsDocs st) of
        Just d  -> "\n  ## " ++ d
        Nothing -> ""

docOf :: ReplState -> String -> IO ()
docOf st name
  | M.member name (rsEnv st) || isAlias =
      case M.lookup name (rsDocs st) of
        Just d  -> putStrLn ("## " ++ d) >> putStrLn renderTypeLine
        Nothing -> putStrLn "(no doc)" >> putStrLn renderTypeLine
  | otherwise = putStrLn $ "unknown name: " ++ name
  where
    isAlias = any ((== name) . aName) (rsAliases st)
              || any ((== name) . dName) (rsDatas st)
    renderTypeLine =
      case [ d | d <- rsDatas st, dName d == name ] of
        (d : _) -> renderData st { rsDocs = M.empty } d
        [] ->
          case M.lookup name (rsEnv st) of
            Just sc -> name ++ " : " ++ showSchemeA (rsAliases st) sc
            Nothing ->
              case [ al | al <- rsAliases st, aName al == name ] of
                (al : _) -> renderAlias st { rsDocs = M.empty } al
                []       -> name


renderStack :: ReplState -> String
renderStack st =
  case rsStack st of
    [] -> "stack: •"
    vs -> "stack: " ++ unwords (map show vs) ++ "  :  " ++ displayTy
  where
    -- pretty display names (a0/ρ0) without touching internal state
    displayTy =
      let Arrow _ o = normalizeArrow (Arrow SEnd (rsStackTy st))
      in showStackA (rsAliases st) o

typeOfWith :: (Arrow -> String) -> ReplState -> String -> IO ()
typeOfWith render st src =
  case parseProgram src >>= inferTermIn (rsEnv st) of
    Left err  -> putStrLn $ "error: " ++ err
    Right arr -> putStrLn $ trim src ++ " : " ++ render (normalizeArrow arr)

handleLine :: ReplState -> String -> IO ReplState
handleLine st line =
  case splitDefs line of
    Left err -> report err
    Right ([(name, _, _)], [], rest)
      | all isSpace rest -> defLine name
    Right ([], [(tyLine, _)], rest)
      | all isSpace rest -> typeLine tyLine
    Right ([], [], _) -> programLine
    Right _           -> report "one definition per line, please"
  where
    report err = putStrLn ("error: " ++ err) >> pure st

    -- type Name(...) = rhs : declare (or replace) a type alias or a
    -- recursive (nominal) data type
    typeLine src =
      case parseTypeLine (rsAliases st) (map dataSig (rsDatas st)) src of
        Left err -> report err
        Right (Left al) -> do
          putStrLn $ "type " ++ aName al
          pure st { rsAliases =
                      al : filter ((/= aName al) . aName) (rsAliases st)
                  , rsDatas =
                      filter ((/= aName al) . dName) (rsDatas st) }
        Right (Right dd) -> do
          let n = dName dd
              redecl = any ((== n) . dName) (rsDatas st)
              envClean
                | redecl    = M.delete n
                                (M.delete ("un" ++ n)
                                  (M.delete ("fold" ++ n) (rsEnv st)))
                | otherwise = rsEnv st
          if M.member n envClean || M.member ("un" ++ n) envClean
            then report $ "Type " ++ n
                   ++ ": constructor name collides with an existing definition"
            else do
              let (scs, runs) = dataDeclArtifacts dd
                  envCtors = foldr (uncurry M.insert) envClean scs
                  st1 = st { rsEnv     = envCtors
                           , rsRun     = M.fromList runs `M.union` rsRun st
                           , rsDatas   = dd : filter ((/= n) . dName)
                                                     (rsDatas st)
                           , rsAliases = filter ((/= n) . aName)
                                                (rsAliases st) }
              putStrLn $ "type " ++ n ++ "   (" ++ n ++ " rolls, un"
                       ++ n ++ " unrolls)"
              case dataFoldSrc dd of
                Nothing -> pure st1
                Just (fn, body) ->
                  case checkModuleWith (M.delete fn (rsEnv st1)) preludeNames
                         (rsAliases st1) (rsDatas st1)
                         ("def " ++ fn ++ " = " ++ body) of
                    Left err -> do
                      putStrLn $ "warning: could not derive " ++ fn
                               ++ ": " ++ err
                      pure st1
                    Right m -> do
                      putStrLn $ "def " ++ fn ++ " : "
                               ++ maybe "?" (showSchemeA (rsAliases st1))
                                    (M.lookup fn (modEnv m))
                      pure st1 { rsEnv = modEnv m
                               , rsRun = moduleRunDefs m `M.union` rsRun st1 }

    -- def name = program : extend (or replace) a user definition;
    -- prelude names may always be shadowed
    defLine name = do
      let envBase
            | name `elem` rsUserDefs st = M.delete name (rsEnv st)
            | otherwise                 = rsEnv st
      case checkModuleWith envBase preludeNames (rsAliases st) (rsDatas st) line of
        Left err -> report err
        Right m  ->
          case modDefs m of
            [(n, sc, _)] -> do
              putStrLn $ "def " ++ n ++ " : " ++ showSchemeA (rsAliases st) sc
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
