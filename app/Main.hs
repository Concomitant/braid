module Main (main) where

import MiniConcatTypechecker
import Control.Monad.Except (runExceptT, liftEither)
import qualified Data.Map as M
import Data.Char (isSpace, isAlphaNum)
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
  , rsUse      :: [String]   -- ambient `use` scope: a session-wide body
  }

initialState :: ReplState
initialState =
  ReplState (modEnv preludeModule)
            (moduleRunDefs preludeModule)
            (modAliases preludeModule)
            (modDatas preludeModule)
            (modDocs preludeModule)
            [] SEnd [] []

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
          loop st { rsStackTy = SEnd, rsStack = [], rsUse = [] }
        ":s" -> do
          liftIO $ do
            putStrLn (renderStack st)
            case rsUse st of
              [] -> pure ()
              ns -> putStrLn ("ambient: use " ++ unwords ns)
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
              liftIO (typeOfWith (showArrowA (dispOf st)) st (drop 3 l))
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

-- the REPL's display context: structural aliases, and the nominal
-- resources whose wires fold onto the arrow as `=Name>`
dispOf :: ReplState -> Disp
dispOf st = Disp (rsAliases st) [ dName d | d <- rsDatas st, dResource d ]

trim :: String -> String
trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

-- a parameter as the user wrote it: a name, or `...` for the stack
-- parameter (its kind shows in the body, not the list)
renderParam :: TyParam -> String
renderParam (PStack _) = "..."
renderParam q          = pName q

renderData :: ReplState -> DataDecl -> String
renderData st d =
  "type " ++ dName d ++ params ++ " = " ++ showTyA noDisp (dBody d) ++ docSuffix
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
  "type " ++ aName al ++ params ++ " = " ++ showTyA noDisp (aBody al) ++ docSuffix
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
    Just sc -> "def " ++ name ++ " : " ++ showSchemeA (dispOf st) sc
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
            Just sc -> name ++ " : " ++ showSchemeA (dispOf st) sc
            Nothing ->
              case [ al | al <- rsAliases st, aName al == name ] of
                (al : _) -> renderAlias st { rsDocs = M.empty } al
                []       -> name


renderStackTy :: ReplState -> String
renderStackTy st =
  let Arrow _ o _ = normalizeArrow (arrPure SEnd (rsStackTy st))
  in showStackA (dispOf st) o

renderStack :: ReplState -> String
renderStack st =
  case rsStack st of
    [] -> "stack: •"
    vs -> "stack: " ++ unwords (map show vs) ++ "  :  " ++ displayTy
  where
    -- pretty display names (a0/ρ0) without touching internal state
    displayTy =
      let Arrow _ o _ = normalizeArrow (arrPure SEnd (rsStackTy st))
      in showStackA (dispOf st) o

typeOfWith :: (Arrow -> String) -> ReplState -> String -> IO ()
typeOfWith render st src =
  case parseProgram src >>= inferTermIn (rsEnv st) of
    Left err  -> putStrLn $ "error: " ++ err
    Right arr -> putStrLn $ trim src ++ " : " ++ render (normalizeArrow arr)

handleLine :: ReplState -> String -> IO ReplState
handleLine st line
  -- `use` at the top level.  In a file the body is the rest of the
  -- block; in a session there is no rest yet, so a bare `use` line opens
  -- a scope over every LATER line — the session is the body.  This is
  -- selection, not sugar: it is what ML's `open` does.
  | ("use" : names) <- words (trim line), all plainName names =
      case names of
        [] -> do
          putStrLn "left the ambient scope"
          pure st { rsUse = [] }
        _ | Just bad <- firstUnknown names -> do
              putStrLn $ "error: `use`: " ++ bad ++ " is not a resource \
                         \(a REPL session cannot declare theories, so \
                         \instances are file-only)"
              pure st
          | otherwise -> do
              putStrLn ("ambient: use " ++ unwords names
                        ++ "   (:clear or a bare `use` to leave)")
              pure st { rsUse = names }
  where
    plainName n = not (null n) && all (\c -> isAlphaNum c || c == '_') n
    firstUnknown ns =
      case [ n | n <- ns
               , not (any (\d -> dName d == n && dResource d) (rsDatas st)) ] of
        (n : _) -> Just n
        []      -> Nothing

handleLine st line =
  case splitDefs line of
    Left err -> report err
    Right ([(name, _, _)], [], [], rest)
      | all isSpace rest -> defLine name
    Right ([], [(tyLine, _)], [], rest)
      | all isSpace rest -> typeLine tyLine
    Right ([], [], [], _) -> programLine
    -- theory/instance are block declarations: they need a whole module
    Right (_, _, (_ : _), _) ->
      report "theory and instance are file declarations — put them in a \
             \.braid file rather than a REPL line"
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
                               ++ maybe "?" (showSchemeA (dispOf st1))
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
              putStrLn $ "def " ++ n ++ " : " ++ showSchemeA (dispOf st) sc
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
        Right (newTy, term) -> do
          r <- evalLine term
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

    -- REPL program lines go through the same elaboration a file's do:
    -- `use` is written out between parse and infer.  Without this a
    -- `use` on a program line reached inference unelaborated.
    elabLine src = do
      term0 <- parseProgram src
      elabUseWith (rsEnv st) []
        (case rsUse st of { [] -> term0 ; ns -> Use ns term0 })

    -- The CHECKED term is the term that runs: a splice site's stamp is
    -- written during inference, so re-elaborating for the run would
    -- discard it and leave the splice unchecked.
    checkLine = do
      term0 <- elabLine line
      (Arrow i o _, term1) <-
        inferTermStamped (rsEnv st) (numberSplices (rsEnv st) term0)
      case solve [CEqStack i (rsStackTy st)] of
        Right s -> pure ( apply s o
                        , mapStamps' (\_ d -> fmap (apply s) d) term1 )
        Left _ ->
          -- the mismatch is against the persistent REPL stack: say so
          Left $ "this line needs input stack '"
               ++ showStackA (dispOf st)
                    (let Arrow i' _ _ = normalizeArrow (arrPure i SEnd) in i')
               ++ "' but the current stack is '"
               ++ renderStackTy st
               ++ "'  (:s to inspect, :clear to reset, or pass it along with ...)"

    evalLine term =
      runExceptT (evalTerm (rsEnv st) (rsRun st) M.empty term (rsStack st))

-- Rename the stack type's free variables into a namespace the inference
-- fresh-name generator (a0…, ρ0…) can never produce, so vars surviving
-- across REPL lines (empty lists, quotations) don't collide with the
-- next line's fresh vars.
freshenStackTy :: SType -> SType
freshenStackTy sty =
  let (tvs0, svs0, rvs0, nvs0, evs) = varsOfStack sty
      -- an existential is a CONSTANT: freshening it would make a boxed
      -- splice's result flexible again on the next line
      tvs = filter (not . isRigidT) tvs0
      svs = filter (not . isRigidS) svs0
      rvs = filter (not . isRigidR) rvs0
      nvs = filter (not . isRigidN) nvs0
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
