module Main (main) where

import MiniConcatTypechecker
import Control.Monad.Except (runExceptT, liftEither)
import qualified Data.Map as M
import qualified Data.Set as S
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
  loaded <- loadSource path
  case loaded of
    Left err -> do
      hPutStrLn stderr $ "error: " ++ err
      exitFailure
    Right src -> runLoaded src

runLoaded :: String -> IO ()
runLoaded src = do
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
  , rsSlots    :: SlotTable  -- instance name -> its theory and slots
  , rsFuncs    :: [(String, String)]    -- functor name -> its word
  , rsTheories :: [Theory]   -- theories `:import` brought in
  , rsTmpls    :: TemplateTable         -- templates awaiting an instance
    -- a session cannot DECLARE a theory or a functor, but `:import` can
    -- bring them in, and then `use` must know them
  }

initialState :: ReplState
initialState =
  ReplState (modEnv preludeModule)
            (moduleRunDefs preludeModule)
            (modAliases preludeModule)
            (modDatas preludeModule)
            (modDocs preludeModule)
            [] SEnd [] [] [] [] [] []

repl :: IO ()
repl = do
  hSetBuffering stdout NoBuffering
  putStrLn "Braid REPL — each line runs against the current stack."
  putStrLn "Commands: :t <prog> type (:t! raw), :doc <name>, :import \"f.braid\", :s stack, :defs, :clear, :q quit"
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
            mapM_ (\(n, (th, _)) ->
                     putStrLn ("def " ++ n ++ " : template over " ++ th))
                  (reverse (rsTmpls st))
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
          | ":import " `isPrefixOf` l ->
              liftIO (importLine st (trim (drop 8 l))) >>= loop
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

-- what a session's lines are checked on top of: everything it has
-- accumulated, including the instances and functors `:import` brought in
baseOf :: ReplState -> ModuleBase
baseOf st =
  (moduleBase (rsEnv st) (rsRun st) preludeShadowNames (rsAliases st)
              (rsDatas st))
    { mbSlots = rsSlots st, mbFuncs = rsFuncs st
    , mbTheories = rsTheories st, mbTemplates = rsTmpls st }

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
      ++ case dataFoldArtifact d of
           Just (fn, sc, _, _) ->
             "\n  " ++ fn ++ " : " ++ showSchemeA (dispOf st) sc
           Nothing -> ""

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

-- A session's lines are ELABORATED before they are inferred: `use` is
-- written out between parse and infer, ambient scope included.  `:t`
-- goes through exactly the same door as a program line — without it an
-- ambient `use Inst` did not resolve slot names for `:t` (`use IntSum`
-- then `:t op` said "Unknown primitive: op"), and a template, whose
-- whole existence is elaboration-time, could not be inspected at all.
elabIn :: ReplState -> String -> Either String Term
elabIn st src = do
  term0 <- parseProgram src
  elabUseWith (ElabCtx (rsEnv st) (rsRun st) (rsSlots st) (rsFuncs st)
                       (rsTmpls st) (map thName (rsTheories st)))
    (case rsUse st of { [] -> term0 ; ns -> Use ns term0 })

typeOfWith :: (Arrow -> String) -> ReplState -> String -> IO ()
typeOfWith render st src =
  case elabIn st src >>= inferTermIn (rsEnv st) of
    Left err  -> putStrLn $ "error: " ++ err
    Right arr -> putStrLn $ trim src ++ " : " ++ render (normalizeArrow arr)

-- `:import "path.braid"` — the file's DECLARATIONS, in this session's
-- scope.  Its main program is not run (a library's demo is its own
-- business), and its own imports are resolved first, exactly as in a
-- file.  This is also the only way a session gets a theory, an instance
-- or a functor, since it cannot declare one.
importLine :: ReplState -> String -> IO ReplState
importLine st arg =
  case parseImportLine ("import " ++ arg) of
    Left err -> putStrLn ("error: " ++ err) >> pure st
    Right path -> do
      loaded <- loadDecls path
      case loaded of
        Left err -> putStrLn ("error: " ++ err) >> pure st
        Right src ->
          case checkModuleWith (baseOf st) src
                 >>= \m -> (,) m <$> moduleSlotTable m of
            Left err -> putStrLn ("error: in " ++ path ++ ": " ++ err)
                          >> pure st
            Right (m, slots) -> do
              let names = [ n | (n, _, _) <- modDefs m ]
                  shadowed = map aName (modAliases m) ++ map dName (modDatas m)
                  st' = st
                    { rsEnv      = modEnv m
                    , rsRun      = buildRunDefs (rsRun st) m
                    , rsAliases  = modAliases m
                                     ++ filter ((`notElem` shadowed) . aName)
                                               (rsAliases st)
                    , rsDatas    = modDatas m
                                     ++ filter ((`notElem` shadowed) . dName)
                                               (rsDatas st)
                    , rsDocs     = modDocs m `M.union` rsDocs st
                    , rsUserDefs = rsUserDefs st
                                     ++ [ n | n <- names
                                            , n `notElem` rsUserDefs st ]
                    , rsSlots    = slots ++ rsSlots st
                    , rsFuncs    = modFunctors m ++ rsFuncs st
                    , rsTheories = modTheories m
                    , rsTmpls    = modTemplates m
                    }
              putStrLn $ "imported " ++ path ++ "   ("
                       ++ intercalate ", " (filter (not . null)
                            [ count (length names) "def"
                            , count (length (modDatas m) + length (modAliases m)) "type"
                            , count (length (modInstances m)) "instance"
                            , count (length (modFunctors m)) "functor"
                            , count (length (modTemplates m)
                                       - length (rsTmpls st)) "template" ])
                       ++ ")"
              pure st'
  where
    count 0 _    = ""
    count n what = show n ++ " " ++ what ++ (if n == 1 then "" else "s")

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
        _ | (t : _) <- [ n | n <- names
                              , n `elem` map thName (rsTheories st) ] -> do
              putStrLn $ "error: `use`: " ++ t ++ " is a theory, and only a \
                         \def's own header may name one — that is what makes \
                         \the def a template"
              pure st
          | Just bad <- firstUnknown names -> do
              putStrLn $ "error: `use`: " ++ bad ++ " is not a resource, \
                         \instance or functor in scope (a session cannot \
                         \declare theories or functors — `:import` a file \
                         \that does)"
              pure st
          | otherwise -> do
              putStrLn ("ambient: use " ++ unwords names
                        ++ "   (:clear or a bare `use` to leave)")
              pure st { rsUse = names }
  where
    plainName n = not (null n) && all (\c -> isAlphaNum c || c == '_') n
    firstUnknown ns =
      case [ n | n <- ns
               , not (any (\d -> dName d == n && dResource d) (rsDatas st))
               , n `notElem` map fst (rsSlots st)
               , n `notElem` map fst (rsFuncs st) ] of
        (n : _) -> Just n
        []      -> Nothing

handleLine st line =
  case splitDefs line of
    Left err -> report err
    Right ([(name, _, _)], [], [], [], rest)
      | all isSpace rest -> defLine name
    Right ([], [(tyLine, _)], [], [], rest)
      | all isSpace rest -> typeLine tyLine
    Right ([], [], [], [], _) -> programLine
    -- theory/instance are block declarations: they need a whole module
    Right (_, _, (_ : _), _, _) ->
      report "theory and instance are file declarations — put them in a \
             \.braid file rather than a REPL line"
    Right (_, _, _, (_ : _), _) ->
      report "import is a file declaration — `:import \"path.braid\"` brings \
             \one into a session"
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
              -- the structural recursor is one of the declaration's
              -- artifacts now, so it needs no derivation step here
              case dataFoldArtifact dd of
                Nothing -> pure st1
                Just (fn, fsc, _, fdoc) -> do
                  putStrLn $ "def " ++ fn ++ " : " ++ showSchemeA (dispOf st1) fsc
                  pure st1 { rsDocs = M.insert fn fdoc (rsDocs st1) }

    -- def name = program : extend (or replace) a user definition;
    -- prelude names may always be shadowed
    defLine name = do
      let envBase
            | name `elem` rsUserDefs st = M.delete name (rsEnv st)
            | otherwise                 = rsEnv st
      case checkModuleWith (baseOf st)
             { mbEnv = envBase
             , mbTemplates = filter ((/= name) . fst) (rsTmpls st) } line of
        Left err -> report err
        Right m  ->
          case modDefs m of
            -- a template is not a def: it never enters the environment,
            -- so it comes back in the template table instead
            [] | Just (th, _) <- lookup name (modTemplates m) -> do
                   putStrLn $ "template " ++ name ++ " over " ++ th
                            ++ "   (`use <instance>` to call it)"
                   pure st { rsTmpls = modTemplates m
                           , rsDocs  = modDocs m `M.union` rsDocs st }
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

    -- The CHECKED term is the term that runs: elaborating twice would
    -- run something other than what was checked.
    checkLine = do
      term1 <- elabIn st line
      Arrow i o _ <- inferTermIn (rsEnv st) term1
      case solve [CEqStack i (rsStackTy st)] of
        Right s -> pure (apply s o, term1)
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
             (zip evs [ Eff S.empty (Just (EV ("_e" ++ show n)))
                      | n <- [0 :: Int ..] ])
      Arrow sty' _ _ = substOnce (Subst tm sm rm nm em) (arrPure sty SEnd)
  in sty'
