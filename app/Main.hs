module Main (main) where

import MiniConcatTypechecker
import Control.Monad.Except (runExceptT, liftEither)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Char (isSpace, isAlphaNum)
import Data.Maybe (isJust)
import Data.List (isPrefixOf, intercalate)
import Data.Bifunctor (first)
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
    Right (src, lmap) -> runLoaded lmap src

runLoaded :: LineMap -> String -> IO ()
runLoaded lmap src = do
  res <- runModuleAt lmap src
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
  , rsUse      :: [String]   -- ambient `with` scope: a session-wide body
  , rsSlots    :: SlotTable  -- model name -> its theory and slots
  , rsFuncs    :: [(String, String)]    -- functor name -> its word
  , rsTheories :: [Theory]   -- theories `:import` brought in
  , rsTmpls    :: TemplateTable         -- templates awaiting a model
  , rsTrans    :: [Transport] -- carrier models `:import` brought in
  , rsKWords   :: [(String, String)]   -- def -> the category it is a word of
  , rsBases    :: [BaseInstance]        -- models of `Base` it imported
  , rsFamilies :: [Instance]  -- parameterized models `:import` brought in
  , rsModels   :: [Instance]  -- ...and the models, members included
  , rsTransformations :: [TransformationInfo]
                         -- transformations it imported, with their verdicts
  , rsRouted   :: [(String, String)]    -- defs INFERRED routing routed
                                        -- (stage 7b), and why -- `:t!`
                                        -- says so
    -- a session cannot DECLARE a theory, a model or a functor, but
    -- `:import` can bring them in, and then `with` must know them
  }

initialState :: ReplState
initialState =
  ReplState (modEnv preludeModule)
            (moduleRunDefs preludeModule)
            (modAliases preludeModule)
            (modDatas preludeModule)
            (modDocs preludeModule)
            [] SEnd [] [] [] [] (modTheories preludeModule) [] [] [] []
            [] [] [] []

repl :: IO ()
repl = do
  hSetBuffering stdout NoBuffering
  putStrLn "Braid REPL — each line runs against the current stack."
  putStrLn "Commands: :t <prog> type (:t! raw), :tc <prog> the type of the Code it leaves, :doc <name>, :import \"f.braid\", :s stack, :defs, :transformations, :clear, :q quit"
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
              ns -> putStrLn ("ambient: with " ++ unwords ns)
          loop st
        ":defs" -> do
          liftIO $ do
            -- `@` is the compiler's character: a model's slots, a
            -- table's insides and a resource's generated carrier and
            -- images are all named with it, and source may not write
            -- one.  `:defs` lists what you can NAME (stage 7b).
            let own n = '@' `notElem` n
            mapM_ (putStrLn . renderData st)
                  (filter (own . dName) (reverse (rsDatas st)))
            mapM_ (putStrLn . renderAlias st)
                  (filter (own . aName) (reverse (rsAliases st)))
            let preludeOnly = filter (`notElem` rsUserDefs st) preludeNames
            mapM_ (putStrLn . renderDef st) preludeOnly
            mapM_ (putStrLn . renderDef st) (filter own (rsUserDefs st))
            mapM_ (\(n, (th, _)) ->
                     putStrLn ("def " ++ n ++ " : template over " ++ th))
                  (reverse (rsTmpls st))
            -- a FAMILY is not a def and not a model: it is what `with
            -- F(M)` applies, so `:defs` says how to apply it
            mapM_ (putStrLn . renderFamily) (reverse (rsFamilies st))
          loop st
        ":transformations" -> do
          liftIO $ case rsTransformations st of
            [] -> putStrLn "no transformations in scope   (:import a file \
                           \that declares one)"
            ms -> mapM_ (putStrLn . renderTransformation) ms
          loop st
        l | ":t! " `isPrefixOf` l -> do
              liftIO $ do
                typeOfWith show st (drop 4 l)
                -- INFERRED ROUTING says why, where the raw arrow is
                -- what you asked for: the resource the def was routed
                -- for, and the atom that originated it (stage 7b).
                case lookup (trim (drop 4 l)) (rsRouted st) of
                  Just why -> putStrLn ("  " ++ why)
                  Nothing  -> pure ()
              loop st
          | ":t " `isPrefixOf` l -> do
              liftIO (typeOfWith (showArrowA (dispOf st)) st (drop 3 l))
              loop st
          | ":tc " `isPrefixOf` l -> do
              liftIO (typeOfCodeWith st (drop 4 l))
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
-- accumulated, including the models and functors `:import` brought in
baseOf :: ReplState -> ModuleBase
baseOf st =
  (moduleBase (rsEnv st) (rsRun st) preludeShadowNames (rsAliases st)
              (rsDatas st))
    { mbSlots = rsSlots st, mbFuncs = rsFuncs st
    , mbTheories = rsTheories st, mbTemplates = rsTmpls st
    , mbTrans = rsTrans st, mbKWords = rsKWords st
    , mbBases = rsBases st
    -- a PARAMETERIZED model an `:import` brought in, and the members
    -- already minted out of it: a second import may apply the one and
    -- must not mint the others twice
    , mbFamilies = rsFamilies st, mbGenerated = rsModels st }

-- the REPL's display context: structural aliases, and the nominal
-- resources whose wires fold onto the arrow as `=Name>`
dispOf :: ReplState -> Disp
dispOf st = Disp (rsAliases st)
                 -- `IO`'s carrier is ABSTRACT and the elaborator never
                 -- writes it, so this row never folds anything; it is
                 -- here because the table is every carriered label,
                 -- and `IO` is one of them (stage 7b).
                 ((ioLabel, ioCarrier)
                  : [ (dName d, dName d) | d <- rsDatas st, dResource d ]
                  ++ [ (tpName m, tpCarrier m) | m <- rsTrans st ])

-- ...and what the REFLECTION words read in a session (2026-09-16): the
-- same four tables, so `:type`, `declOf` and `typeOfCode` all answer
-- over the session's own prefix scope
replRCtx :: ReplState -> RCtx
replRCtx st = RCtx (rsEnv st) (rsDatas st) (rsAliases st) (rsTheories st)

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
      -- the projections a named declaration generates are ordinary
      -- words, so they are listed exactly as the recursor is
      ++ concat [ "\n  " ++ f ++ " : " ++ showSchemeA (dispOf st) sc
                | ((f, sc), _) <- dataFieldArtifacts d ]
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
  -- THE DICTIONARY (stage 8).  It is a resource nobody declared, so
  -- nothing in the session's tables answers about it, and it is still
  -- a thing `:doc` must answer about \8212 the more so because what it
  -- has NOT got is the point.
  | name == dictLabel = mapM_ putStrLn dictResourceDoc
  | M.member name (rsEnv st) || isAlias || isObjModel =
      case M.lookup name (rsDocs st) of
        Just d  -> putStrLn ("## " ++ d) >> putStrLn renderTypeLine
                     >> generated >> verdicts
        Nothing -> putStrLn "(no doc)" >> putStrLn renderTypeLine
                     >> generated >> verdicts
  | otherwise = putStrLn $ "unknown name: " ++ name
  where
    -- a transformation's word is a def like any other, and its squares
    -- are one line of its documentation (`:transformations` for the slots)
    verdicts =
      mapM_ (putStrLn . transformationDocLine)
            [ mi | mi <- rsTransformations st, tiName mi == name ]
    -- STAGE 7b: `model R in Doctrine` declares a MODEL OF THE DOCTRINE besides
    -- the wire, and sugar you cannot read is a feature rather than a
    -- desugaring — so `:doc R` prints the three declarations it wrote,
    -- exactly as a `table` shows the `data` line it wrote.
    generated
      | any (\d -> dName d == name && dResource d) (rsDatas st) =
          mapM_ putStrLn (resourceModelDoc name)
      | otherwise = pure ()
    isAlias = any ((== name) . aName) (rsAliases st)
              || any ((== name) . dName) (rsDatas st)
    -- AN OBJECT-MAPPED MODEL OF `Base` DECLARES NO WORD (stage 7c) —
    -- its action on a literal is not a rename, so there is no `Code ⇒
    -- Code` table — and it is still a declaration `:doc` must answer
    -- about.
    isObjModel = any (\b -> inName b == name && not (null (inObjMap b)))
                     (rsBases st)
    renderTypeLine =
      case [ d | d <- rsDatas st, dName d == name ] of
        (d : _) -> renderData st { rsDocs = M.empty } d
        [] ->
          case M.lookup name (rsEnv st) of
            Just sc -> name ++ " : " ++ showSchemeA (dispOf st) sc
            Nothing ->
              case [ al | al <- rsAliases st, aName al == name ] of
                (al : _) -> renderAlias st { rsDocs = M.empty } al
                [] | isObjModel ->
                       "model " ++ name ++ " in Base — applied with `with "
                         ++ name ++ "`, and no word: an object-mapped model "
                         ++ "is an elaboration-time functor"
                   | otherwise -> name


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

-- A session's lines are ELABORATED before they are inferred: `with` is
-- written out between parse and infer, ambient scope included.  `:t`
-- goes through exactly the same door as a program line — without it an
-- ambient `with Inst` did not resolve slot names for `:t` (`with IntSum`
-- then `:t op` said "Unknown primitive: op"), and a template, whose
-- whole existence is elaboration-time, could not be inspected at all.
elabIn :: ReplState -> String -> Either String Term
elabIn st src = do
  term0 <- parseProgramIn (rsDatas st) src
  elabHeaders (ElabCtx (rsEnv st) (rsRun st) (rsSlots st) (rsFuncs st)
                       (rsTmpls st) (map thName (rsTheories st))
                       (rsTrans st)
                       (rsKWords st) (rsBases st) [] False
                       -- a session declares no `table` of its own: one is
                       -- a file declaration, and `:import` brings in only
                       -- the two words it generates
                       Nothing []
                       [ dName d | d <- rsDatas st, dResource d ]
                       (replRCtx st))
    (case rsUse st of { [] -> term0 ; ns -> With Transporting ns term0 })

typeOfWith :: (Arrow -> String) -> ReplState -> String -> IO ()
typeOfWith render st src =
  case first (locFor [] src) (elabIn st src >>= inferTermIn (rsEnv st)) of
    Left err  -> putStrLn $ "error: " ++ err
    Right arr -> putStrLn $ trim src ++ " : " ++ render (normalizeArrow arr)

-- `:tc <prog>` — the type of the CODE the line produces (2026-09-16).
-- A different question from `:t`, not a second spelling of it:
-- `:t [dup ; +] ; getCode` is `\8226 \8658 Code`, and what you wanted to know
-- is `Int \8658 Int`.  The line is RUN (against the session's stack, which
-- it leaves alone) and `typeOfCode` is asked about the one value it
-- left \8212 so the command is the word, and nothing else.
typeOfCodeWith :: ReplState -> String -> IO ()
typeOfCodeWith st src =
  case first (locFor [] src) (elabIn st src) of
    Left err -> putStrLn $ "error: " ++ err
    Right term -> do
      r <- runExceptT (evalTerm (replRCtx st) (rsRun st) M.empty term
                                (rsStack st))
      case r of
        Left err -> putStrLn $ "error: " ++ err
        Right (out, logs) -> do
          mapM_ putStrLn logs
          case out of
            [c] -> say c
            _   -> putStrLn $ "error: `:tc` wants a line that leaves exactly \
                              \one Code value, and this one left "
                           ++ show (length out) ++ " wire(s)"
  where
    say c = putStrLn $ trim src ++ " : "
                    ++ either ("error: " ++) id
                         (typeOfCodeV (replRCtx st) c >>= showTypeV (replRCtx st))

-- `:import "path.braid"` — the file's DECLARATIONS, in this session's
-- scope.  Its main program is not run (a library's demo is its own
-- business), and its own imports are resolved first, exactly as in a
-- file.  This is also the only way a session gets a theory, a model
-- or a functor, since it cannot declare one.
importLine :: ReplState -> String -> IO ReplState
importLine st arg =
  case parseImportLine ("import " ++ arg) of
    Left err -> putStrLn ("error: " ++ err) >> pure st
    Right path -> do
      loaded <- loadDecls path
      case loaded of
        Left err -> putStrLn ("error: " ++ err) >> pure st
        Right (src, lmap) ->
          case checkModuleWithAt lmap (baseOf st) src
                 >>= \m -> (,) m <$> moduleSlotTable m of
            -- the refusal already names the file and line it came off,
            -- so the session does not say `in <path>` a second time
            Left err -> putStrLn ("error: " ++ err) >> pure st
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
                    , rsTrans    = modTrans m
                    , rsKWords   = modKWords m
                    , rsBases    = modBases m
                    , rsFamilies = modFamilies m
                    , rsModels   = modInstances m
                    , rsTransformations   = modTransformations m
                                     ++ [ mi | mi <- rsTransformations st
                                             , tiName mi `notElem`
                                                 map tiName (modTransformations m) ]
                    , rsRouted   = modRouted m
                                     ++ [ r | r <- rsRouted st
                                            , fst r `notElem`
                                                map fst (modRouted m) ]
                    }
              putStrLn $ "imported " ++ path ++ "   ("
                       ++ intercalate ", " (filter (not . null)
                            [ count (length names) "def"
                            , count (length (modDatas m) + length (modAliases m)) "type"
                            , models (length (modInstances m))
                                     (length (modTrans m))
                            , count (length (modFamilies m))
                                    "parameterized model" 
                            , count (length (modFunctors m)) "functor"
                            , count (length (modTemplates m)
                                       - length (rsTmpls st)) "template"
                            , count (length (modTransformations m))
                                    "transformation" ])
                       ++ ")"
              pure st'
  where
    count 0 _    = ""
    count n what = show n ++ " " ++ what ++ (if n == 1 then "" else "s")
    -- a model with a carrier is one of the models, not a second kind of
    -- declaration: say so rather than counting it twice
    models 0 _ = ""
    models n 0 = count n "model"
    models n k = count n "model" ++ " (" ++ show k ++ " with a carrier)"

handleLine :: ReplState -> String -> IO ReplState
handleLine st line
  -- `with` at the top level.  In a file it is a def's header clause; in
  -- a session there is no def yet, so a bare `with` line opens a scope
  -- over every LATER line — the session is the body.  This is
  -- selection, not sugar: it is what ML's `open` does.
  | ("with" : names) <- words (trim line), all plainName names =
      case names of
        [] -> do
          putStrLn "left the ambient scope"
          pure st { rsUse = [] }
        _ | (t : _) <- [ n | n <- names
                              , n `elem` map thName (rsTheories st) ] -> do
              putStrLn $ "error: `with " ++ t ++ "` names a theory: `with` \
                         \applies a functor, and a theory is not one — a def \
                         \whose own header is `in " ++ t ++ "` is a \
                         \template over it"
              pure st
          | Just bad <- firstUnknown names -> do
              putStrLn $ "error: `with`: " ++ bad ++ " is not a resource, \
                         \model or functor in scope (a session cannot \
                         \declare theories, models or functors — \
                         \`:import` a file that does)"
              pure st
          | otherwise -> do
              putStrLn ("ambient: with " ++ unwords names
                        ++ "   (:clear or a bare `with` to leave)")
              pure st { rsUse = names }
  where
    -- ...and an APPLIED model is a name too: `with Fwd(Floats)` names
    -- the member `Fwd(Floats)`, which an imported file already minted
    plainName n = not (null n)
               && all (\c -> isAlphaNum c || c `elem` ("_(), " :: String)) n
    firstUnknown ns =
      case [ n | n <- ns
               , not (any (\d -> dName d == n && dResource d) (rsDatas st))
               , n `notElem` map fst (rsSlots st)
               , n `notElem` map fst (rsFuncs st)
               , n `notElem` map inName (rsBases st) ] of
        (n : _) -> Just n
        []      -> Nothing

handleLine st line =
  case splitDefs line of
    Left err -> report err
    Right ([(name, _, _, _)], [], [], [], [], rest)
      | all isSpace rest -> defLine name
    Right ([], [(tyLine, _)], [], [], [], rest)
      -- `model R in Doctrine = Ty` DECLARES A MODEL OF THE DOCTRINE
      -- (stage 7b, spelled this way since 2026-09-18) — a carrier, a
      -- theory and the model — so a session's resource line goes
      -- through the module checker, which is the one place that
      -- generation lives.  A `type`/`data` line still takes the short
      -- path: it generates no declaration beyond its own.
      | all isSpace rest, isJust (doctrineCarrierName tyLine) ->
          resourceLine tyLine
      | all isSpace rest -> typeLine tyLine
    Right ([], [], [], [], [], _) -> programLine
    -- theory/model/functor are block declarations: they need a whole
    -- module
    Right (_, _, (_ : _), _, _, _) ->
      report "theory, model and functor are file declarations — \
             \put them in a .braid file rather than a REPL line"
    Right (_, _, _, (_ : _), _, _) ->
      report "import is a file declaration — `:import \"path.braid\"` brings \
             \one into a session"
    -- a table reads a FILE at check time, so it needs a file to be
    -- resolved against
    Right (_, _, _, _, (_ : _), _) ->
      report "table is a file declaration — put it in a .braid file and \
             \`:import` that, so the CSV resolves against the file"
    Right _           -> report "one definition per line, please"
  where
    report err = putStrLn ("error: " ++ err) >> pure st

    -- `model R in Doctrine = rhs`: the wire, AND the model its
    -- declaration generates.  Checked as a one-line module so a session
    -- and a file agree about what a resource is.
    resourceLine src =
      case checkModuleWith (baseOf st) src
             >>= \m -> (,) m <$> moduleSlotTable m of
        Left err -> report err
        Right (m, slots) -> do
          let n = case words src of (_ : nm : _) -> takeWhile (/= '(') nm
                                    _            -> src
              shadowed = map aName (modAliases m) ++ map dName (modDatas m)
          putStrLn $ "type " ++ n ++ "   (" ++ n ++ " rolls, un"
                   ++ n ++ " unrolls, and a model of Doctrine — `:doc "
                   ++ n ++ "`)"
          pure st
            { rsEnv      = modEnv m
            , rsRun      = buildRunDefs (rsRun st) m
            , rsAliases  = modAliases m
                             ++ filter ((`notElem` shadowed) . aName)
                                       (rsAliases st)
            , rsDatas    = modDatas m
                             ++ filter ((`notElem` shadowed) . dName)
                                       (rsDatas st)
            , rsDocs     = modDocs m `M.union` rsDocs st
            , rsSlots    = slots ++ rsSlots st
            , rsTheories = modTheories m
            , rsTrans    = modTrans m
                             ++ [ t | t <- rsTrans st
                                    , tpName t `notElem` map tpName (modTrans m) ]
            , rsModels   = modInstances m
            }

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
          -- BY NAME, not by count: a session carries its models, and a
          -- model's slot defs are regenerated on every line — as are a
          -- resource's two images since stage 7b — so `modDefs` holds
          -- more than the one the user just wrote.
          case [ d | d@(n, _, _) <- modDefs m, n == name ] of
            -- a template is not a def: it never enters the environment,
            -- so it comes back in the template table instead
            [] | Just (th, _) <- lookup name (modTemplates m) -> do
                   putStrLn $ "template " ++ name ++ " in " ++ th
                            ++ "   (`with <model>` to call it)"
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
                  -- a session def written under `with K` is a K-word from
                  -- here on, exactly as it would be in a file
                , rsKWords   = modKWords m
                  -- ...and one INFERRED ROUTING routed says so to `:t!`
                , rsRouted   = modRouted m
                                 ++ [ r | r <- rsRouted st
                                        , fst r `notElem` map fst (modRouted m) ]
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
      runExceptT (evalTerm (replRCtx st) (rsRun st) M.empty term (rsStack st))

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
