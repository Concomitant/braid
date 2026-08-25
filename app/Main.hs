module Main (main) where

import MiniConcatTypechecker
import Control.Monad.Except (runExceptT, liftEither)
import qualified Data.Map as M
import Data.Char (isSpace)
import Data.List (isPrefixOf, intercalate)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO
import System.Console.Haskeline
import Control.Monad.IO.Class (liftIO)

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
  res <- runModule src
  case res of
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
  runInputT defaultSettings (loop initialState)

-- haskeline supplies line editing, history (up-arrow), and ctrl-d;
-- everything the branches DO stays in IO, lifted per line
loop :: ReplState -> InputT IO ()
loop st = do
  mline <- getInputLine "braid> " >>= traverse continueOpen
  case mline of
    Nothing        -> pure ()          -- EOF / ctrl-d
    Just Nothing   -> loop st          -- ctrl-d abandoned a continuation
    Just (Just line) ->
      case trim line of
        ""      -> loop st
        ":q"    -> pure ()
        ":quit" -> pure ()
        ":clear" -> do
          liftIO (putStrLn "stack cleared")
          loop st { rsStackTy = SEnd, rsStack = [] }
        ":s" -> do
          liftIO (putStrLn (renderStack st))
          loop st
        ":defs" -> do
          liftIO $ do
            mapM_ (putStrLn . renderData st) (reverse (rsDatas st))
            mapM_ (putStrLn . renderAlias st) (reverse (rsAliases st))
            let preludeOnly = filter (`notElem` rsUserDefs st) preludeNames
            mapM_ (putStrLn . renderDef st) preludeOnly
            mapM_ (putStrLn . renderDef st) (rsUserDefs st)
          loop st
        l | ":t! " `isPrefixOf` l -> do
              liftIO (typeOfWith show st (drop 4 l))
              loop st
          | ":t " `isPrefixOf` l -> do
              liftIO (typeOfWith (showArrowA (rsAliases st)) st (drop 3 l))
              loop st
          | ":doc " `isPrefixOf` l -> do
              liftIO (docOf st (trim (drop 5 l)))
              loop st
          | ":" `isPrefixOf` l -> do
              liftIO (putStrLn ("unknown command: " ++ l))
              loop st
          | otherwise -> liftIO (handleLine st l) >>= loop

-- A bracket may span line breaks, so keep reading while one is open.
-- Ctrl-d during a continuation abandons the buffer (Nothing).
continueOpen :: String -> InputT IO (Maybe String)
continueOpen line = go (lineDepth line) line
  where
    go d acc
      | d <= 0 = pure (Just acc)
      | otherwise = do
          mnext <- getInputLine "braid| "
          case mnext of
            Nothing   -> pure Nothing
            Just next -> go (d + lineDepth next) (acc ++ "\n" ++ next)

trim :: String -> String
trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

-- a parameter as the user wrote it: a name, or `...` for the stack
-- parameter (its kind shows in the body, not the list)
renderParam :: TyParam -> String
renderParam (PStack _) = "..."
renderParam q          = pName q

renderData :: ReplState -> DataDecl -> String
renderData st d =
  "type " ++ dName d ++ params ++ " = " ++ showTyA [] (dBody d) ++ docSuffix
  where
    params
      | null (dParams d) = ""
      | otherwise =
          "(" ++ intercalate ", " (map renderParam (dParams d)) ++ ")"
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
          "(" ++ intercalate ", " (map renderParam (aParams al)) ++ ")"
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


renderStackTy :: ReplState -> String
renderStackTy st =
  let Arrow _ o _ = normalizeArrow (arrPure SEnd (rsStackTy st))
  in showStackA (rsAliases st) o

renderStack :: ReplState -> String
renderStack st =
  case rsStack st of
    [] -> "stack: •"
    vs -> "stack: " ++ unwords (map show vs) ++ "  :  " ++ displayTy
  where
    -- pretty display names (a0/ρ0) without touching internal state
    displayTy =
      let Arrow _ o _ = normalizeArrow (arrPure SEnd (rsStackTy st))
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
                           , rsRun     = extendRunDefs (rsRun st)
                                           [ (nm, ar, op, t)
                                           | (nm, (ar, op, t)) <- runs ]
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
                               , rsRun = buildRunDefs (rsRun st1) m }

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
                , rsRun      = buildRunDefs (rsRun st) m
                , rsDocs     = modDocs m `M.union` rsDocs st
                , rsUserDefs =
                    rsUserDefs st ++ [n | n `notElem` rsUserDefs st]
                }
            _ -> report "internal: expected exactly one definition"

    -- a program line: typecheck against the current stack, then run
    programLine =
      case checkLine of
        Left err -> report err
        Right newTy -> do
          r <- evalLine
          case r of
            Left err -> report ("runtime error: " ++ err)
            Right (stack', logs)
              | Just e <- desyncError newTy stack' ->
                  mapM_ putStrLn logs >> report ("runtime error: " ++ e)
              | otherwise -> do
                  mapM_ putStrLn logs
                  let st' = st { rsStackTy = freshenStackTy newTy
                               , rsStack   = stack' }
                  putStrLn (renderStack st')
                  pure st'

    checkLine = do
      term <- parseProgram line
      Arrow i o _ <- inferTermIn (rsEnv st) term
      case solve [CEqStack i (rsStackTy st)] of
        Right s -> pure (apply s o)
        Left _ ->
          -- the mismatch is against the persistent REPL stack: say so
          Left $ "this line needs input stack '"
               ++ showStackA (rsAliases st)
                    (let Arrow i' _ _ = normalizeArrow (arrPure i SEnd) in i')
               ++ "' but the current stack is '"
               ++ renderStackTy st
               ++ "'  (:s to inspect, :clear to reset, or pass it along with ...)"

    evalLine = runExceptT $ do
      term <- liftEither (parseProgram line)
      evalTerm (rsEnv st) (rsRun st) M.empty term (rsStack st)

-- Rename the stack type's free variables into a namespace the inference
-- fresh-name generator (a0…, ρ0…) can never produce, so vars surviving
-- across REPL lines (empty lists, quotations) don't collide with the
-- next line's fresh vars.
freshenStackTy :: SType -> SType
freshenStackTy sty =
  let (tvs, svs, rvs, nvs, evs) = varsOfStack sty
      tm = M.fromList
             (zip tvs [ TVarTy (TV ("_a" ++ show n)) | n <- [0 :: Int ..] ])
      sm = M.fromList
             (zip svs [ STail (SV ("_r" ++ show n)) | n <- [0 :: Int ..] ])
      rm = M.fromList
             (zip rvs [ RTail (RV ("_s" ++ show n)) | n <- [0 :: Int ..] ])
      nm = M.fromList
             (zip nvs [ Exp 0 (Just (NV ("_n" ++ show n))) | n <- [0 :: Int ..] ])
      em = M.fromList
             (zip evs [ Eff False (Just (EV ("_e" ++ show n)))
                      | n <- [0 :: Int ..] ])
      Arrow sty' _ _ = substOnce (Subst tm sm rm nm em) (arrPure sty SEnd)
  in sty'
