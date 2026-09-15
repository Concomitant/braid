-- Test suite: run via `cabal test`.
module Main (main) where

import MiniConcatTypechecker
import Data.List (isInfixOf, isPrefixOf, isSuffixOf, sort)
import System.Exit (exitFailure, exitSuccess)
import System.Directory (listDirectory)

-- Every examples/*.braid must run without error (catches rot: an
-- unknown prim, a type error, a desync).  Output-regression checking
-- is a future enhancement; "runs clean" is the high-value signal.
runExample :: String -> IO (Maybe String)
runExample name = do
  loaded <- loadSource ("examples/" ++ name)
  case loaded of
    Left err  -> pure (Just ("examples/" ++ name ++ ": " ++ err))
    Right (src, lmap) -> do
      r <- runModuleAt lmap src
      pure $ case r of
        Right _  -> Nothing
        Left err -> Just ("examples/" ++ name ++ ": " ++ err)

-- TRANSFORMATION VERDICTS (2026-09-14).  What the checker decided about
-- each square is STORED on the module, so `:transformations` reads it
-- rather than deciding it again; these pin the stored verdicts for the
-- two example files that declare transformations.  `proved` is
-- `sameCode`, for every input; `sampled (n points; why)` is the theory's
-- own evidence, and `why` is what the normalizer said instead of `true`.
-- (example file, transformation, the rendering `:transformations` prints)
transformationVerdictTests :: [(String, String, String)]
transformationVerdictTests =
    -- a hom-object carrier pins its own `Fn` to one wire per side, so
    -- an internal functor's squares normalize outright
  [ ( "transformations.braid", "Forget"
    , unlines' [ "Forget : Names \8658 Funcs"
               , "  embed    proved"
               , "  compose  proved"
               , "  first    proved"
               , "  observe  proved"
               , "  sample   proved" ] )
    -- ...and `len` is a fold, which applies its handler, so two squares
    -- stop at `ev` of an open wire and the third at `pack`: all three go
    -- to the samples, each carrying the reason it had to
  , ( "transformations.braid", "Len"
    , unlines' [ "Len : ListMonoid \8658 IntSum"
               , "  unit    sampled (ev of an open wire)"
               , "  op      sampled (2 points; ev of an open wire)"
               , "  sample  sampled (`pack` has no closed arity)" ] )
    -- forgetting the tangent: every square proved, which is the
    -- strongest verdict the machinery has — and the model is now
    -- `Fwd(Floats)`, a MEMBER of the family `model Fwd(R : Smooth(a, g))`
    -- minted by `use Fwd(Floats)`, which a transformation names exactly
    -- as it names any other model (2026-09-15) — `gradient` included, since
    -- 2026-09-14: its result type is a theory PARAMETER, so `Value` has
    -- a second component (the zero map) and the square that says
    -- "forgetting a tangent zeroes it" normalizes outright
  , ( "autodiff.braid", "Value"
    , unlines' [ "Value : Fwd(Floats) \8658 Floats"
               , "  add       proved"
               , "  mul       proved"
               , "  neg       proved"
               , "  lit       proved"
               , "  exp       proved"
               , "  sin       proved"
               , "  cos       proved"
               , "  sample    proved"
               , "  observe   proved"
               , "  gradient  proved" ] )
    -- and the transpose: `lit` must prove (its input is a `Float`, so
    -- no `sample` reaches it), the five operations are decided at the
    -- samples THROUGH THE EXIT, since a `Rev` holds a closure.  Their
    -- reason is `sameCode` answering FALSE rather than refusing: the two
    -- sides are different programs of the FREE category, equal only up
    -- to the arithmetic of the uninterpreted `fadd` and `fmul`, which is
    -- exactly what the theory's evidence is for
  , ( "autodiff.braid", "Transpose"
    , unlines' [ "Transpose : Fwd(Floats) \8658 Rev"
               , "  add       sampled (2 points; differ in the free category)"
               , "  mul       sampled (2 points; differ in the free category)"
               , "  neg       sampled (1 point; differ in the free category)"
               , "  lit       proved"
               , "  exp       sampled (1 point; differ in the free category)"
               , "  sin       sampled (1 point; differ in the free category)"
               , "  cos       sampled (1 point; differ in the free category)"
               , "  sample    proved"
               , "  observe   proved"
                 -- THE GRADIENT HALF, machine-checked at last: the two
                 -- ends of `gradient : a \8658 g` sit at DIFFERENT
                 -- theory parameters, so the square needs a component
                 -- at each — `transpose` at `a`, `gx` at `g`.  It is
                 -- compared at `Grad` directly (two Floats, which `eq?`
                 -- reaches) rather than through `observe`, which is an
                 -- exit for `a` and not for `g`.
               , "  gradient  sampled (1 point; differ in the free category)" ] )
    -- EXPECTATION, as a homomorphism of the CONVEX structure
    -- (2026-09-15).  It is not a functor of the Markov category —
    -- E[g(X)] is not g(E[X]), and `examples/prob.braid` §12 prints the
    -- counterexample — so the transformation it does admit is declared
    -- at `theory Convex(m)`, one carrier, the fair mixture.  Every
    -- square goes to the samples: `mix` and `observe` stop at the `ev`
    -- a fold makes of its handler, and the two evidence slots at
    -- `Box`, whose arity is open.
  , ( "prob.braid", "Expect"
    , unlines' [ "Expect : Mixtures \8658 Means"
               , "  mix      sampled (2 points; ev of an open wire)"
               , "  sample   sampled (`Box` has no closed arity)"
               , "  other    sampled (`Box` has no closed arity)"
               , "  observe  sampled (1 point; ev of an open wire)" ] )
  ]
  where unlines' = foldr1 (\a b -> a ++ "\n" ++ b)

runTransformationVerdicts :: (String, String, String) -> IO (Maybe String)
runTransformationVerdicts (file, name, expected) = do
  loaded <- loadSource ("examples/" ++ file)
  pure $ case loaded >>= \(src, lmap) -> checkModuleAt lmap src of
    Left err -> Just (file ++ " (" ++ name ++ "): " ++ err)
    Right m  ->
      case [ mi | mi <- modTransformations m, tiName mi == name ] of
        []       -> Just (file ++ ": no transformation " ++ name)
        (mi : _)
          | renderTransformation mi == expected -> Nothing
          | otherwise -> Just (file ++ ": expected\n" ++ expected
                                    ++ "\ngot\n" ++ renderTransformation mi)

-- IMPORTS (stage 4¾).  A file's declarations in another file's scope:
-- textual inclusion, so a type, a resource, a theory, a model and a
-- functor all cross the boundary with no machinery of their own —
-- and so does a template, since it is a table entry like the rest.
-- Fixtures live in test/imports/ and are loaded from disk, since the
-- whole point is the file context.
-- (path, expected print log, expected final stack rendering)
importTests :: [(String, [String], String)]
importTests =
    -- defs, a resource, a model, a functor and a RULE SET, all
    -- imported; the imported file's own main does NOT run
    -- …and a TEMPLATE: declared over a theory in one file, instantiated
    -- by a `use` in another
  [ ("uses-util.braid", ["28", "12", "81", "50", "0", "20"], "")
    -- a diamond includes the shared file once
  , ("diamond.braid",   ["7", "8", "10"], "")
    -- a library file still runs as a program, main and all
  , ("util.braid",      ["util.braid's own main — NOT run when imported"], "")
  ]

-- (path, expected error fragment)
importFailTests :: [(String, String)]
importFailTests =
  [ ("cycle-a.braid", "import cycle: cycle-a.braid → cycle-b.braid → cycle-a.braid")
    -- the inclusion is injective on names or it is an error, and the
    -- error names both files
  , ("clash.braid",   "`double` is already defined in test/imports/util.braid")
  , ("missing.braid", "import: no such file: nope.braid (looked in \
                      \test/imports/nope.braid and in the current directory)")
    -- a module checked without a file context cannot import
  , ("bad-syntax.braid", "Malformed import")
    -- LOCATIONS (2026-09-15).  A refusal in an imported file names THAT
    -- file and THAT line, not the assembled source the loader built.
  , ("uses-broken.braid",
     "test/imports/broken-dep.braid:4, in def snapped: \
     \Cannot unify types: Str vs Int")
    -- ...and a main-program refusal names the line of the STAGE that
    -- failed, not the line the program starts on
  , ("mainline.braid",
     "test/imports/mainline.braid:4: Cannot unify types: Str vs Int")
  ]

-- TABLES (stage 6c part 3).  `table Trades = "x.csv"` is a declaration
-- the LOADER resolves: the path by the import rule, the whole file read
-- at check time, and Braid text spliced in under the line.  Fixtures
-- live in test/tables/ and are loaded from disk, since the whole point
-- is the file context.
-- (path, expected print log, expected final stack rendering)
tableTests :: [(String, [String], String)]
tableTests =
    -- the sniff: Int, then Float (a column mixing `2` with `1.5`), then
    -- Str.  The three folds only type if all three are right.
  [ ("sniff.braid",    ["0", "3.0", "abc", "3"], "")
    -- the schema form: a positional rename and a written type, one form
  , ("over.braid",     ["100.0", "annbob", "Full Name"], "")
    -- the loader RE-READS at runtime, so a file that no longer matches
    -- puts its first bad row on the miss track, by line number
  , ("badrow.braid",   ["bad row on line 3"], "")
    -- a table crosses a file boundary: the CSV resolves against the
    -- IMPORTING file's directory, and the library's own main is dropped
  , ("uses-lib.braid", ["1", "2"], "")
  ]

-- (path, expected error fragment)
tableFailTests :: [(String, String)]
tableFailTests =
    -- a blank cell is refused, naming line and column: a column has ONE
    -- type and a blank is not a value of it
  [ ("blank.braid",   "line 2, column 2 `b`): the cell is blank")
    -- a column name is a WORD, so it collides like one — and the fix
    -- the message names is the schema form
  , ("clash.braid",   "field name 'len' is already a word in scope")
  , ("clash.braid",   "rename the column with the schema form")
    -- a header that is not a word after sanitizing
  , ("nonword.braid", "is not a word after sanitizing")
    -- the schema is positional, so its arity must match the header's
  , ("arity.braid",   "the schema writes 2 columns but the header has 3")
    -- the path rule is the import's, and so is the error
  , ("missing.braid", "table Gone: no such file: nope.csv")
    -- the helpers are the compiler's spelling: source may not name one
  , ("hidden.braid",  "is the compiler's spelling of a table's insides")
  ]

-- What `:import` sees: a table's declarations, generated, with the
-- library's own main dropped.  (path, fragment, whether it must appear)
tableImportTests :: [(String, String, Bool)]
tableImportTests =
  [ ("lib.braid", "def loadLib = ", True)
  , ("lib.braid", "def headerLib = ", True)
  , ("lib.braid", "99 ; print", False)
  ]

runTable :: (String, [String], String) -> IO (Maybe String)
runTable (name, wantLog, wantStack) = do
  loaded <- loadSource ("test/tables/" ++ name)
  case loaded of
    Left err  -> pure (Just (name ++ ": " ++ err))
    Right (src, lmap) -> do
      r <- runModuleAt lmap src
      pure $ case r of
        Left err -> Just (name ++ ": " ++ err)
        Right (stack, logs)
          | logs /= wantLog ->
              Just (name ++ ": expected log " ++ show wantLog
                         ++ ", got " ++ show logs)
          | unwords (map show stack) /= wantStack ->
              Just (name ++ ": expected stack " ++ show wantStack
                         ++ ", got " ++ show (unwords (map show stack)))
          | otherwise -> Nothing

runTableFail :: (String, String) -> IO (Maybe String)
runTableFail (name, frag) = do
  loaded <- loadSource ("test/tables/" ++ name)
  err <- case loaded of
    Left e    -> pure (Just e)
    Right (src, lmap) -> do
      r <- runModuleAt lmap src
      pure (either Just (const Nothing) r)
  pure $ case err of
    Nothing -> Just (name ++ ": expected failure containing " ++ show frag)
    Just e
      | frag `isInfixOf` e -> Nothing
      | otherwise -> Just (name ++ ": expected " ++ show frag ++ ", got: " ++ e)

runTableImport :: (String, String, Bool) -> IO (Maybe String)
runTableImport (name, frag, want) = do
  loaded <- loadDecls ("test/tables/" ++ name)
  pure $ case loaded of
    Left err -> Just (name ++ ": " ++ err)
    Right (src, _)
      | (frag `isInfixOf` src) == want -> Nothing
      | want      -> Just (name ++ ": expected " ++ show frag ++ " in the \
                                  \imported declarations")
      | otherwise -> Just (name ++ ": " ++ show frag ++ " must not be \
                                  \imported")

runImport :: (String, [String], String) -> IO (Maybe String)
runImport (name, wantLog, wantStack) = do
  loaded <- loadSource ("test/imports/" ++ name)
  case loaded of
    Left err  -> pure (Just (name ++ ": " ++ err))
    Right (src, lmap) -> do
      r <- runModuleAt lmap src
      pure $ case r of
        Left err -> Just (name ++ ": " ++ err)
        Right (stack, logs)
          | logs /= wantLog ->
              Just (name ++ ": expected log " ++ show wantLog
                         ++ ", got " ++ show logs)
          | unwords (map show stack) /= wantStack ->
              Just (name ++ ": expected stack " ++ show wantStack
                         ++ ", got " ++ show (unwords (map show stack)))
          | otherwise -> Nothing

runImportFail :: (String, String) -> IO (Maybe String)
runImportFail (name, frag) = do
  loaded <- loadSource ("test/imports/" ++ name)
  err <- case loaded of
    Left e    -> pure (Just e)
    Right (src, lmap) -> do
      r <- runModuleAt lmap src
      pure (either Just (const Nothing) r)
  pure $ case err of
    Nothing -> Just (name ++ ": expected failure containing " ++ show frag)
    Just e
      | frag `isInfixOf` e -> Nothing
      | otherwise -> Just (name ++ ": expected " ++ show frag ++ ", got: " ++ e)

-- (source, expected alpha-normalized type)
passTests :: [(String, String)]
passTests =
  [ -- literals are terminal-source constants (• ⇒ Int, no implicit remainder)
    ("17",            "• ⇒ Int")
  , ("1 2",           "• ⇒ Int Int")
  , ("1 2 3",         "• ⇒ Int Int Int")
  , ("1 ...",         "ρ0 ⇒ Int ρ0")     -- explicit remainder: push onto any stack
    -- pushing over existing wires: _ covers exactly one, ... covers any
  , ("2 _",           "a0 ⇒ Int a0")
  , ("1 >> 2 _",      "• ⇒ Int Int")
  , ("1 >> 2 ...",    "• ⇒ Int Int")
  , ("1 >> 2 \8230",  "• ⇒ Int Int")   -- U+2026 … aliases ...
    -- FLOAT (2026-09-14): a base type beside Int, sharing no word with
    -- it.  A literal is digits `.` digits, terminal-source exactly as
    -- an Int literal is.
  , ("2.0",           "• ⇒ Float")
  , ("0.5",           "• ⇒ Float")
  , ("-2.5",          "• ⇒ Float")
  , ("2.0 ...",       "ρ0 ⇒ Float ρ0")
  , ("2.0 3.5 >> fadd", "• ⇒ Float")
  , ("fsub",          "Float Float ⇒ Float")
  , ("fmul",          "Float Float ⇒ Float")
  , ("fdiv",          "Float Float ⇒ Float")
  , ("fexp",          "Float ⇒ Float")
  , ("fsin",          "Float ⇒ Float")
  , ("fcos",          "Float ⇒ Float")
  , ("fsqrt",         "Float ⇒ Float")
    -- the comparison is a ROUTER, exactly as `lt?` is
  , ("flt?",          "Float Float ⇒ (Float Float | Float Float)")
    -- `eq?` is the polymorphic one and reaches a Float; there is no
    -- second spelling of equality
  , ("2.0 2.0 >> eq?", "• ⇒ (Float Float | Float Float)")
    -- the two crossings, written where they are meant
  , ("toFloat",       "Int ⇒ Float")
  , ("floor",         "Float ⇒ Int")
  , ("2 >> toFloat",  "• ⇒ Float")
  , ("2.5 >> floor",  "• ⇒ Int")
  , ("+",             "Int Int ⇒ Int")
  , ("pass",          "ρ0 ⇒ ρ0")

    -- cartesian basis (exact: no implicit remainder on operations either)
  , ("swap",          "a0 a1 ⇒ a1 a0")
  , ("dup",           "a0 ⇒ a0 a0")
  , ("drop",          "a0 ⇒ •")
    -- `_` is THE identity prim: the section hole, marking where the
    -- incoming wire goes.  `id` is the WORD for it and is a prelude def
    -- (2026-09-12 prim-reduction pass), so it is checked below with the
    -- rest of the prelude.
  , ("_",             "a0 ⇒ a0")
  , ("2 _ >> *",      "Int ⇒ Int")
  , ("_ 2 >> -",      "Int ⇒ Int")
  , ("_ drop",        "a0 a1 ⇒ a0")

    -- sequencing; increment needs the explicit remainder (1 >> + is ill-typed)
  , ("1 ... >> +",    "Int ⇒ Int")
  , ("1 2 >> +",      "• ⇒ Int")
    -- LINES THAT WRAP (2026-09-14).  A newline is a strict `>>`, so
    -- writing the `>>` too — at the end of a line or the start of the
    -- next — is redundant rather than wrong; both used to be `Expected
    -- a tensor stage, got: TokSeq`.  A `\` is the third form: it drops
    -- the newline outright, so the tensor stage itself wraps.
  , ("1 2 >>\n+",      "• ⇒ Int")
  , ("1 2\n>> +",      "• ⇒ Int")
  , ("1 2 ;\n+",       "• ⇒ Int")
  , ("1 2\n; +",       "• ⇒ Int")
  , ("1 \\\n2 >> +",    "• ⇒ Int")
  , ("(1 \\\n2) >> +",  "• ⇒ Int")
  , ("[1 \\\n2 >> +] >> ev", "• ⇒ Int")
    -- the `|`-led row is untouched: a newline before `|` is still a
    -- stage break, so a row whose arms are one per line still reads as
    -- one row
  , ("5 >> alt1 >> (dup >> * | ---)\n| ---\nmerge", "• ⇒ Int")
    -- strict tensor: `1 +` is (• ⇒ Int) ⊗ (Int Int ⇒ Int), NOT increment
  , ("1 +",           "Int Int ⇒ Int Int")
  , ("1 2 >> (1 ... >> +) (2 _ >> *) >> + >> print", "• =IO> •")

    -- newline is strict >>
  , ("1 2\n(1 ... >> +) (2 _ >> *)\n+\nprint", "• =IO> •")
  , ("1 2\n\n+",                 "• ⇒ Int")   -- blank lines collapse

    -- a bracket may span lines: a newline against a delimiter's inner
    -- edge is layout, absorbed.  A newline BETWEEN stages inside the
    -- bracket is still a strict >> (see the failTest for `(1\n2)`).
  , ("(\n1 2\n)",                "• ⇒ Int Int")  -- one stage, two wires
  , ("(1\n1 ... >> +)",          "• ⇒ Int")      -- two stages: 1 >> (1 ... >> +)
  , ("[\ndup >> *\n]",           "• ⇒ Fn⟨Int ⇒ Int⟩")
  , ("(\n(\n1\n)\n)",            "• ⇒ Int")      -- nests
    -- ; is a synonym for >>
  , ("1 2 ; +",                  "• ⇒ Int")
  , ("dup ; * ; toStr",          "Int ⇒ Str")
  , ("5;dup;*",                  "• ⇒ Int")   -- no whitespace needed

    -- worked schemes from the spec (now exact, matching it verbatim)
  , ("dup >> *",      "Int ⇒ Int")           -- square
  , ("_ drop",        "a0 a1 ⇒ a0")          -- first
  , ("dup >> _ drop", "a0 ⇒ a0")             -- counit law
  , ("dup >> swap",   "a0 ⇒ a0 a0")          -- commutativity law
  , ("swap >> swap",  "a0 a1 ⇒ a0 a1")       -- involution

    -- trailing remainder: ... and >>> (ops are exact, so deep stacks need it too)
  , ("1 2 3 >> (1 ... >> +) ... >> + ...",  "• ⇒ Int Int")
  , ("1 2 3 >> (1 ... >> +) >>> + ...",     "• ⇒ Int Int")   -- >>> ≡ the ... form
  , ("1 2 3\n(1 ... >> +) ...\n+ ...", "• ⇒ Int Int")   -- same, via newlines
  , ("...",                      "ρ0 ⇒ ρ0")       -- bare remainder stage

    -- quotations and ev (quotes are terminal-source constants)
  , ("[dup >> *]",               "• ⇒ Fn⟨Int ⇒ Int⟩")
  , ("[dup >> *] 7 >> ev",    "• ⇒ Int")
  , ("[dup >> *] 7 >> ev >> print", "• =IO> •")   -- spec example (49)
  , ("ev",                    "Fn⟨ρ0 ⇒ ρ1⟩ ρ0 ⇒ ρ1")

    -- grouping: (p) is the open program p, never reified
  , ("(dup >> *)",       "Int ⇒ Int")
  , ("7 >> (dup >> *)",  "• ⇒ Int")
  , ("(1 4 5)",          "• ⇒ Int Int Int")
  , ("(1 ... >> +)",     "Int ⇒ Int")          -- the increment
  , ("(1 ... >> +) (2 _ >> *)",   "Int Int ⇒ Int Int")  -- compound closed non-finally
  , ("(2 _ >> *) (1 ... >> +)",   "Int Int ⇒ Int Int")  -- compound open finally
  , ("(pass >> drop) (1 ... >> +)", "a0 Int ⇒ Int")       -- linked tails close soundly

    -- named open abstractions (spec examples, exact types)
  , ("(x -> x)",              "a0 ⇒ a0")
  , ("(x y -> x)",            "a0 a1 ⇒ a0")        -- projection ≡ id drop
  , ("(x y -> y x)",          "a0 a1 ⇒ a1 a0")     -- ≡ swap
  , ("(x -> x x >> *)",       "Int ⇒ Int")          -- named square ≡ dup >> *
  , ("(x -> x 1 >> +)",       "Int ⇒ Int")          -- named increment
  , ("(x y -> x y >> +)",     "Int Int ⇒ Int")
  , ("(x y -> x x >> * >> y ... >> +)", "Int Int ⇒ Int")  -- reuse + reorder
  , ("(w -> w)",              "a0 ⇒ a0")            -- parameters shadow globals
  , ("[x -> x 1 >> +]",       "• ⇒ Fn⟨Int ⇒ Int⟩")
  , ("[x y -> x]",            "• ⇒ Fn⟨a0 a1 ⇒ a0⟩")
  , ("(x -> [x])",            "a0 ⇒ Fn⟨• ⇒ a0⟩")   -- closure over a parameter

    -- sums: injections, code rows, merge
  , ("alt1",           "ρ0 ⇒ (ρ0 | σ0)")
  , ("alt2",           "ρ0 ⇒ (ρ1 | ρ0 | σ0)")
    -- compositional injections: here starts a sum, there widens it;
    -- here >> there ≡ alt2, exactly
  , ("here",          "ρ0 ⇒ (ρ0 | σ0)")
  , ("there",         "(σ0) ⇒ (ρ0 | σ0)")
  , ("here >> there", "ρ0 ⇒ (ρ1 | ρ0 | σ0)")
  , ("1 2 >> alt1",    "• ⇒ (Int Int | σ0)")
  , ("merge",         "(ρ0 | ρ0) ⇒ ρ0")
  , ("(dup | drop)",  "(a0 | a1) ⇒ (a0 a0 | •)")
  , ("(dup | ---)",   "(a0 | σ0) ⇒ (a0 a0 | σ0)")
  , ("5 >> alt1 >> (dup >> * | ---) >> merge", "• ⇒ Int")
    -- `into`: the OPEN eliminator.  [h, id] — handle the first
    -- alternative into the remaining row, tag-shift the rest.
  , ("into", "Fn⟨ρ0 ⇒ (σ0)⟩ (ρ0 | σ0) ⇒ (σ0)")
  , ("5 >> alt1 >> [toStr >> alt1] ... >> into", "• ⇒ (Str | σ0)")
    -- peel one track off an OPEN row: the residual passes untouched
  , ("[toStr >> alt1] ... >> into", "(a0 | Str | σ0) ⇒ (Str | σ0)")

  , ("[dup >> * | drop]", "• ⇒ Fn⟨(Int | a0) ⇒ (Int | •)⟩")
    -- bare rows: each LINE is a code row (>> binds tighter than |,
    -- | tighter than newline)
    -- open binders: a parameter list uses the stage vocabulary — a name
    -- binds one wire (deepest first), `_` hands one wire to the BODY,
    -- `...` hands it the whole rest.  No `_`/`...` = input-closed (the
    -- original behaviour, unchanged).
  , ("(x ... -> x ...)",         "a0 ρ0 ⇒ a0 ρ0")
  , ("(x ... -> x x ... >> + + >> +)", "Int Int Int ⇒ Int")
  , ("(x _ -> x x _ >> + _ >> +)",     "Int Int ⇒ Int")
  , ("(a b ... -> a b ... >> + +)",    "Int Int Int Int ⇒ Int Int")
  , ("(x _ z -> z _ x)",         "a0 a1 a2 ⇒ a2 a1 a0")   -- slots are positional
  , ("(_ x -> x _)",             "a0 a1 ⇒ a1 a0")

    -- the NAMING binder `-> x y z`: identity on the wires it names —
    -- they stay on the stack and pick up names for the rest of the
    -- scope.  Sugar for `x y z ... -> x y z ...`, so the types match
    -- exactly (compare the line above).  The arrow's SIDE says which
    -- binder it is: names before it are cut, names after it label.
  , ("-> x -> pass",             "a0 ρ0 ⇒ a0 ρ0")
  , ("-> a b -> pass",           "a0 a1 ρ0 ⇒ a0 a1 ρ0")
  , ("5\n-> x\nx ... >> +",      "• ⇒ Int")   -- live wire AND name
  , ("3 4\n-> a b\n* >> drop\na b >> *", "• ⇒ Int")  -- names outlive the wires
  , ("1\n-> x\ndrop\nx",         "• ⇒ Int")   -- a name survives its wire
  , ("2\n-> x\ndup >> *",        "• ⇒ Int")   -- naming nothing is still id
    -- slots use the stage vocabulary: `_` skips a wire, exactly as it
    -- does in `print print _`.  Without it you could only ever name a
    -- prefix, since slots are positional from the deepest wire.
  , ("1 2 3 -> _ _ z -> drop drop drop >> z", "• ⇒ Int")
  , ("1 2 -> a _ -> drop drop >> a",          "• ⇒ Int")
    -- bare and mid-line: the arrow ends the stage it follows
  , ("1 \"a\" .foo -> x _ y -> print print _ >> x ...", "• =IO> Int Sym")
  , ("5 ; -> x -> x ... >> +",   "• ⇒ Int")   -- after a separator
  , ("5 -> n -> n ... >> *",     "• ⇒ Int")   -- explicit body marker
  , ("5\n-> n\nn ... >> *",      "• ⇒ Int")   -- ...or an ordinary stage break
  , ("dup | +",                  "(a0 | Int Int) ⇒ (a0 a0 | Int)")
  , ("dup | +\n+ | _\nmerge",    "(Int | Int Int) ⇒ Int")
  , ("1 ... >> + | ---",         "(Int | σ0) ⇒ (Int | σ0)")
    -- EVERY empty arm is pass, not just first/last — track-column layout
  , ("(drop | |)",               "(a0 | ρ0 | ρ1) ⇒ (• | ρ0 | ρ1)")
  , ("(| | drop)",               "(ρ0 | ρ1 | a0) ⇒ (ρ0 | ρ1 | •)")
  , ("(| drop | | drop |)",      "(ρ0 | a0 | ρ1 | a1 | ρ2) ⇒ (ρ0 | • | ρ1 | • | ρ2)")
    -- consecutive bars are consecutive empty arms (the old || literal
    -- is gone; this is its successor meaning, pinned)
  , ("(|| drop)",                "(ρ0 | ρ1 | a0) ⇒ (ρ0 | ρ1 | •)")

    -- routers: the primitive comparators (predicates are now DERIVED —
    -- their tests live in moduleTypeTests)
  , ("eq?",           "a0 a0 ⇒ (a0 a0 | a0 a0)")
  , ("lt?",           "Int Int ⇒ (Int Int | Int Int)")
  , ("-",             "Int Int ⇒ Int")
    -- strings and symbols
  , ("\"hello\"",     "• ⇒ Str")
  , (".red",          "• ⇒ Sym")
  , ("cat",           "Str Str ⇒ Str")
  , ("toStr",         "a0 ⇒ Str")
  , ("asInt?",        "Str ⇒ (Int | Str)")
  , ("forget",        "ρ0 ⇒ •")
    -- STAGE 5a½: `fix` is the word that may run unbounded, so it MINTS
    -- the `Recursive` label the way `print` mints IO.  `loop` is a prelude
    -- def built on it (2026-09-12) and is checked with the prelude.
    -- loop protocol aliases: again ≡ alt1 (continue), done ≡ alt2 (exit)
  , ("again",         "ρ0 ⇒ (ρ0 | σ0)")
  , ("done",          "ρ0 ⇒ (ρ1 | ρ0 | σ0)")
  ]

-- (source, substring expected in the error)
failTests :: [(String, String)]
failTests =
  [ ("1 true >> +",   "Cannot unify types")
  , ("true >> (1 ... >> +)",     "Cannot unify types")
    -- nothing has an implicit remainder: 1 makes exactly one wire,
    -- + consumes exactly two
  , ("1 >> +",        "Cannot unify stacks")
  , ("1 >> 2",        "Cannot unify stacks")   -- the incoming wire is uncovered
  , ("1 2 3 >> +",    "Cannot unify stacks")   -- deep stack needs `+ ...`
  , ("7 >> [1]",      "Cannot unify stacks")   -- write `[1] ...` instead
    -- Γ inside Fn⟨…⟩: binding Γ := Fn⟨Γ⇒Δ⟩ ρ must fail the occurs
    -- check now that it traverses element types.
  , ("dup >> ev",  "Occurs check")
    -- FLOAT: no numeric tower and no overloading, so a mixed stage is
    -- a clash, and the refusal names the two vocabularies and the two
    -- crossings rather than a coercion that does not exist
  , ("1 2.0 >> +",     "no numeric tower")
  , ("1.0 2 >> fadd",  "no numeric tower")
  , ("2 2 >> fmul",    "no numeric tower")
  , ("2.0 >> floor >> fsqrt", "no numeric tower")
    -- one Float literal notation, so the other one is refused where it
    -- is written
  , ("1e-3",           "Exponent notation is not a Float literal")
  , ("2.5e3 >> print", "Exponent notation is not a Float literal")
  , ("[dup",          "Unclosed quotation")
  , ("]",             "Expected a tensor stage")
  , ("(1",            "Unclosed group")
    -- list elements must be pure pushes
  , ("list(1, 2)",   "Unclosed group")   -- the literal is GONE: bare ident + a comma in a group
  , ("dup ... drop",       "'...' must be the final atom")
  , ("1 >",           "Unexpected '>'")
    -- a DANGLING continuation, both ways round (2026-09-14): a `\` that
    -- is not the last thing on its line, and one with no line after it
  , ("1 \\ 2",         "must be the last thing on its line")
  , ("1 2 \\\n",       "the next line must have something on it")
  , ("nonsense42x",   "Unknown primitive")
  , ("",              "Expected a tensor stage")
    -- sums
  , ("5 >> alt1 >> (1 | ---)",  "Cannot unify stacks")   -- alt • vs Int
    -- `| ...` MEANT the residual until 2026-09-12.  Refused for one
    -- release rather than re-read, so no old row silently changes
    -- meaning; the message names both replacements.
  , ("(dup | ...)",
     "`| ...` used to mean the residual; write `| ---` for more alternatives, or `| pass` for a third track that passes")
  , ("1 ... >> + | ...", "used to mean the residual")
  , ("(dup | --- | drop)", "'| ---' must end its row")
  , ("1 >> (dup | drop)",      "Cannot unify types")    -- Int vs a sum wire
    -- scope rules: unresolved names are errors, never inferred parameters
  , ("(x -> y)",      "Unknown primitive: y")
  , ("[x 1 >> +]",    "Unknown primitive: x")   -- no inferred-parameter quotation
  , ("(x -> +)",      "Cannot unify stacks")    -- body must be input-closed
  , ("(x x -> x)",    "Duplicate parameter")
    -- open binders: parameter-list ordering, and everything-exact still
    -- applies to the wires `_` hands to the body
  , ("(x ... y -> x)", "must be the last parameter")
  , ("(_ x -> x)",     "Cannot unify stacks")   -- the `_` wire is unaccounted for
  , ("(x _ -> x)",     "Cannot unify stacks")   -- the `_` wire is unaccounted for
    -- the naming binder takes names only, and like `x y ->` it opens a
    -- stage (its body is the rest of the scope)
  , ("-> x x -> pass", "Duplicate parameter")
  , ("-> x ... -> pass", "'...' is implicit")
  , ("-> -> pass",     "needs at least one name")
    -- a binder whose body is empty binds names nothing can reach; the
    -- cutting form fails the same way (`def f = x ->` has no body)
  , ("5 -> x",         "ends its scope")
  , ("[5 -> x]",       "ends its scope")
  , ("(-> x)",         "ends its scope")   -- the parenthesized form is gone
  , ("1 -> x 2",       "must be followed by its body")
    -- a newline inside a bracket is NOT deleted, only absorbed at the
    -- delimiters: `(1 ⏎ 2)` is `(1 >> 2)`, which is exact-arity nonsense
  , ("(1\n2)",         "Cannot unify stacks")
  ]

-- (module source, expected alpha-normalized type of main)
-- THE FAMILY every stage-6f test is written against: one theory, one
-- ordinary model, and `Fwd` — a model PARAMETERIZED by a model, whose
-- slot bodies are templates over the PARAMETER's theory.
famSrc :: String
famSrc =
  "theory Ring(a) =\n\
\    add    : a a \8658 a\n\
\    mul    : a a \8658 a\n\
\    lit    : Float \8658 a\n\
\    sample : \8226 \8658 a\n\
\    observe : a \8658 Float\n\
\    law addComm = (sample (2.0 ; lit) ; add ; observe) ((2.0 ; lit) sample ; add ; observe) ; eq? ; verdict\n\
\model Floats : Ring(Float) =\n\
\    add = fadd\n\
\    mul = fmul\n\
\    lit = id\n\
\    sample = 1.5\n\
\    observe = id\n\
\data Dual(a) = a a\n\
\model Fwd(R : Ring(a)) : Ring(Dual(a)) =\n\
\    add = Dual(x, dx) Dual(y, dy) -> (x y ; add) (dx dy ; add) ; Dual\n\
\    mul = Dual(x, dx) Dual(y, dy) -> (x y ; mul) ((x dy ; mul) (dx y ; mul) ; add) ; Dual\n\
\    lit = (c -> (c ; lit) (0.0 ; lit) ; Dual)\n\
\    sample = sample (1.0 ; lit) ; Dual\n\
\    observe = Dual(v, t) -> v ; observe\n\
\def cube = over Ring ; (x -> ((x x ; mul) x ; mul) (1.0 ; lit) ; add)\n\
\def tangent = Dual(v, t) -> t\n"

-- ...and the same family with its `add` broken on the VALUE side.  A
-- family cannot be audited once: that would need equality modulo the
-- parameter theory's laws.  Its laws run AT EACH INSTANTIATION, on the
-- member's own evidence, so this is refused where it is first APPLIED
-- and the refusal names the member — the family and the argument at
-- once, because the applied form is the name.
badFamSrc :: String
badFamSrc = go famSrc
  where
    go str@(c : cs)
      | pat `isPrefixOf` str = "(x x ; add)" ++ drop (length pat) str
      | otherwise            = c : go cs
    go []                    = []
    pat = "(x y ; add)"

-- What `:defs` and `:import` read off a module that declares a family:
-- the family itself (not a def, not a model — it is what `use F(M)`
-- applies), and every MEMBER the module's `use` headers asked for.
-- (source, the `:defs` lines, the model names in order)
familyReportTests :: [(String, [String], [String])]
familyReportTests =
  [ ( famSrc ++ "def d = use Fwd(Floats) ; cube\n\
      \def dd = use Fwd(Fwd(Floats)) ; cube\n\
      \\"ok\" ; print"
    , [ "model Fwd(R : Ring) : Ring   (a FAMILY \8212 apply it: \
        \`use Fwd(<model of Ring>)`)" ]
    , [ "Floats", "Fwd(Floats)", "Fwd(Fwd(Floats))" ] )
  ]

runFamilyReport :: (String, [String], [String]) -> Maybe String
runFamilyReport (src, wantFams, wantModels) =
  case checkModule src of
    Left err -> Just ("family report: " ++ err)
    Right m
      | gotFams == wantFams && gotModels == wantModels -> Nothing
      | otherwise -> Just $ "family report: expected " ++ show wantFams
                         ++ " / " ++ show wantModels ++ ", got "
                         ++ show gotFams ++ " / " ++ show gotModels
      where
        gotFams   = map renderFamily (modFamilies m)
        gotModels = map inName (modInstances m)

moduleTypeTests :: [(String, String)]
moduleTypeTests =
  [ ("def square = dup >> *\nsquare",           "Int ⇒ Int")
    -- A MODEL PARAMETERIZED BY A MODEL (2026-09-15).  `use Fwd(Floats)`
    -- APPLIES the family and mints a member; the receipt on the arrow is
    -- the APPLICATION, one label, because one model read the template.
  , (famSrc ++ "def d = use Fwd(Floats) ; cube\nd",
     "Dual(Float) =Fwd(Floats)> Dual(Float)")
    -- ...and the family applies to a member of ITSELF, which is what
    -- "a functor Mod(T) → Mod(T)" buys: the carrier nests, the slot
    -- bodies are unchanged, and the receipt says which member read it
  , (famSrc ++ "def dd = use Fwd(Fwd(Floats)) ; cube\ndd",
     "Dual(Dual(Float)) =Fwd(Fwd(Floats))> Dual(Dual(Float))")
    -- the head is read by SUBSTITUTION and nothing else: `Ring(Dual(a))`
    -- at `a := Dual(Float)` is the carrier the slots are declared at
  , (famSrc ++ "use Fwd(Fwd(Floats)) ; sample",
     "• =Fwd(Fwd(Floats))> Dual(Dual(Float))")
    -- THE CLOSED STRUCTURE (stage 5a¾).  `ev` is the exponential's
    -- counit — the prim formerly spelled `apply` — and `curry` is the
    -- other half, a prelude def whose own body is the one
    -- binder-into-quote abstraction elimination takes as a generator.
  , ("ev",       "Fn⟨ρ0 ⇒ ρ1⟩ ρ0 ⇒ ρ1")
  , ("curry",    "Fn⟨a0 ρ0 ⇒ ρ1⟩ ⇒ Fn⟨a0 ⇒ Fn⟨ρ0 ⇒ ρ1⟩⟩")
  , ("capture",  "a0 Fn⟨a0 ρ0 ⇒ ρ1⟩ ⇒ Fn⟨ρ0 ⇒ ρ1⟩")
    -- distributivity is a THEOREM here (`P × –` is a left adjoint), and
    -- `dist2`'s body is the derivation; `undist2` needs no closure
  , ("dist2",    "a0 (ρ0 | ρ1) ⇒ (a0 ρ0 | a0 ρ1 | σ0)")
    -- STAGE 5b: the Code-level twin of `sameCode`, and the rule engine
  , ("sameCodeC", "Code Code ⇒ Bool")
    -- a generated PROJECTION is an ordinary word with an ordinary
    -- principal type; the declaration's parameters generalize
  , ("data Trade = (sym: Str, px: Float, qty: Int)\npx", "Trade ⇒ Float")
  , ("data Cell(a) = (val: a, tag: Str)\nval", "Cell(a0) ⇒ a0")
  , ("rewrite",   "List(Sym) List(Sym) Code ⇒ Code")
    -- STAGE 5b: a rule set declares a WORD of its own name and a
    -- FUNCTOR of that name.  `use Opt` mints `=Opt>` like any other
    -- scope, and unions with `Recursive` when the body ties a knot.
  , ("def dupInt = dup >> _ _ 0 >> _ +\nmodel Opt : Base = dupInt = dup\nOpt",
     "Code ⇒ Code")
  , ("def dupInt = dup >> _ _ 0 >> _ +\nmodel Opt : Base = dupInt = dup\n\
     \def p =\n    use Opt\n    dupInt\n    +\np", "Int =Opt> Int")
  , ("def dupInt = dup >> _ _ 0 >> _ +\nmodel Opt : Base = dupInt = dup\n\
     \def sumTo =\n    use Opt\n\
     \    [(self a n -> n >> dupInt >> drop _ >> zero? >> ((z -> a) | (m -> (a m >> +) (m >> _ 1 >> -) >> self ... >> ev)) >> merge)] ...\n\
     \    fix ...\n    ev\nsumTo", "Int Int =Opt Recursive> Int")
  , ("undist2",  "(a0 ρ0 | a0 ρ1) ⇒ a0 (ρ0 | ρ1 | σ0)")
    -- distN follows caseN's arity family, and like caseN the sums nest
  , ("dist3",    "a0 (ρ0 | (ρ1 | ρ2)) ⇒ (a0 ρ0 | (a0 ρ1 | a0 ρ2 | σ0))")
  , ("undist3",  "(a0 ρ0 | (a0 ρ1 | a0 ρ2)) ⇒ a0 (ρ0 | (ρ1 | ρ2 | σ0) | σ1)")
    -- THE FUNCTOR RECEIPT SAYS WHAT RAN (2026-09-12).  `checkFunctorWord`
    -- tests `eIO` alone, so a `Recursive`-labelled functor word runs at
    -- elaboration (fuel-bounded); before this its `Recursive` escaped and the
    -- expansion read `Int =RecId> Int`.  The receipt now carries the
    -- word's own labels beside the functor's name.
  , ("def idRec = [(self c -> c)] ... >> fix ... >> ev\nfunctor RecId = idRec\ndef twice =\n    use RecId\n    dup >> +\ntwice",
     "Int =RecId Recursive> Int")
    -- >=> is Kleisli composition in the sum monad
  , ("even? >=> zero?",                         "Int ⇒ (Int | Int)")
    -- routers, now derived in the prelude from eq?/lt?/mod via the
    -- (n | n) pattern — same closed types as the old prims
  , ("negative?",     "Int ⇒ (Int | Int)")
  , ("odd?",          "Int ⇒ (Int | Int)")
  , ("zero?",         "Int ⇒ (Int | Int)")
    -- sum associators re-nest a decision tree (open tails from alt1/alt2)
  , ("assocL", "(ρ0 | (ρ1 | ρ2)) ⇒ ((ρ0 | ρ1 | σ0) | ρ2 | σ1)")
  , ("assocR", "((ρ0 | ρ1) | ρ2) ⇒ (ρ0 | (ρ1 | ρ2 | σ0) | σ1)")
    -- type aliases: display folding (Bool/Maybe from the prelude;
    -- user aliases beat prelude; fewest-params-bound wins ties)
  , ("5 >> odd? >> verdict",                    "• ⇒ Bool")
    -- the runtime lift of a functor has the program's arrow BY
    -- CONSTRUCTION; the checked interposition is a plain Code word
  , ("lift2",     "Fn⟨Code ⇒ Code⟩ Fn⟨ρ0 ⇒ ρ1⟩ ⇒ Fn⟨ρ0 ⇒ ρ1⟩")
  , ("interpose", "Code Code ⇒ Code")
  , ("7 >> zero? >> (forget | ---)",            "• ⇒ (• | Int)")
    -- 2026-09-12 PRIM REDUCTION.  `id` is the WORD for `_`, and `loop`
    -- is the Elgot dagger built on `fix` — both prelude defs now, with
    -- EXACTLY the schemes they had as prims.  `loop`'s body was briefly
    -- `=Recursive>` because composition unified grades instead of joining
    -- them; stage 5a⁹⁄₁₀ fixed that and the prim's type came back.
  , ("id",                                      "a0 ⇒ a0")
  , ("id drop",                                 "a0 a1 ⇒ a0")
  , ("loop",     "Fn⟨ρ0 ⇒ (ρ0 | ρ1)⟩ ρ0 =Recursive> ρ1")
    -- and the three derived comparators keep the prims' schemes exactly
  , ("gt?",      "Int Int ⇒ (Int Int | Int Int)")
  , ("gte?",     "Int Int ⇒ (Int Int | Int Int)")
  , ("lte?",     "Int Int ⇒ (Int Int | Int Int)")
    -- THE TWO TAILS (5a⅞).  `...` continues WIRES, `---` continues
    -- ALTERNATIVES, and the inferred types already told them apart by
    -- letter: ρ is a track's contents, σ the residual.
  , ("(toStr | not | ---)",  "(a0 | (ρ0 | ρ1) | σ0) ⇒ (Str | (ρ1 | ρ0 | σ1) | σ0)")
  , ("(toStr | not | pass)", "(a0 | (ρ0 | ρ1) | ρ2) ⇒ (Str | (ρ1 | ρ0 | σ0) | ρ2)")
    -- peel one alternative with `into`, then close the ladder with the
    -- existing `otherwise` — the pairing this stage is for
  , ("[toStr >> alt1] ... >> into >> _ [drop >> \"?\"] >> otherwise",
     "(a0 | Str | a1) ⇒ Str")
    -- `---` in a DECLARATION HEAD: the fifth parameter kind.  A written
    -- residual displays as the ordinary σ.
  , ("data Any2(---) = (Int | Str | ---)\nAny2", "(Int | Str | σ0) ⇒ Any2((σ0))")
  , ("data Any2(---) = (Int | Str | ---)\nunAny2", "Any2((σ0)) ⇒ (Int | Str | σ0)")
    -- Fn⟨(A | ---) ⇒ (B | ---)⟩ in a declaration: roll/unroll is the
    -- ascription that forces a quote to that type
  , ("data Peeler(---) = Fn⟨(Int | ---) ⇒ (Str | ---)⟩\n[(s -> s >> (toStr | ---))] >> Peeler >> unPeeler",
     "• ⇒ Fn⟨(Int | σ0) ⇒ (Str | σ0)⟩")
    -- `(---)` — the sum that is ALL residual — is a legal written type;
    -- it is `into`'s result shape
  , ("type Rest(---) = (---)\ntheory Recover(---) =\n    recover : (Str | ---) ⇒ (---)\n7 >> alt1", "• ⇒ (Int | σ0)")
  , ("type MInt = (• | Int)\n7 >> zero? >> (forget | ---)", "• ⇒ MInt")
  , ("type Result(a, e) = (a | e)\nodd?",       "Int ⇒ Result(Int, Int)")
  , ("type YN = Bool\ntrue",                    "• ⇒ YN")
    -- Fn in type declarations: alias naming + display folding, both
    -- the Unicode (Fn⟨…⟩) and ASCII (Fn(… -> …)) spellings
  , ("type Endo(a) = Fn⟨a ⇒ a⟩\n[dup >> *]",     "• ⇒ Endo(Int)")
  , ("type Endo(a) = Fn(a -> a)\n[dup >> *]",     "• ⇒ Endo(Int)")
    -- a written label set is read in a `type` alias too, and the older
    -- io spellings still mean `=IO>`
  , ("type Sink(a) = Fn⟨a =IO> •⟩\n[print]",       "• ⇒ Sink(a0)")
  , ("type Sink(a) = Fn(a ->! •)\n[print]",        "• ⇒ Sink(a0)")
  , ("type Rep(a) = Fn⟨a =Recursive> a⟩\n[[_ 100 >> less?] [2 _ >> *] ... >> while]",
     "• ⇒ Rep(Int)")
    -- and a nested Fn keeps its grade through alias instantiation
  , ("type Run(a) = Fn⟨Fn⟨a =Recursive> a⟩ a =Recursive> a⟩\ndata W = (Run(Int))\nunW",
     "W ⇒ Run(Int)")
  , ("type Pred(a) = Fn⟨a ⇒ (a | a)⟩\n[odd?]",    "• ⇒ Pred(Int)")
    -- a param substituted INSIDE the Fn (substStackVars into TFn), and
    -- folded back on display
  , ("type Thunk(a) = Fn⟨• ⇒ a⟩\n[5]",            "• ⇒ Thunk(Int)")
    -- the polymorphic sum-ladder words: splice (routing), settle /
    -- settleR (the dual ladder steps) — row variables, no arity families
  , ("splice",   "(ρ0 | (σ0)) ⇒ (ρ0 | σ0)")
  , ("settle",   "(ρ0 | (ρ0 | ρ1)) ⇒ (ρ0 | ρ1)")
  , ("settleR",  "((ρ0 | ρ1) | ρ1) ⇒ (ρ0 | ρ1)")
  , ("negative? >> (| zero?) >> splice", "Int ⇒ (Int | Int | Int)")
    -- caseN: the flat coproduct eliminators, now prelude words (the
    -- case(…) special form is REMOVED — quoted handlers, sum on top)
  , ("[drop >> \"neg\"] [drop >> \"zero\"] [toStr] ... >> case3", "(a0 | (a1 | a2)) ⇒ Str")
  , ("[dup >> +] [drop >> 3] ... >> case2",       "(Int | a0) ⇒ Int")
    -- codata: recursion THROUGH a Fn makes the type nominal; the
    -- constructor carries the thunked tail
  , ("data Stream(a) = (a Fn⟨• ⇒ Stream(a)⟩)\nStream",
        "a0 Fn⟨• ⇒ Stream(a0)⟩ ⇒ Stream(a0)")
    -- …and a written label set is read back sorted, in a `data`
    -- declaration like anywhere else: this is the thunk a `fix`-built
    -- producer actually fills (examples/stream.braid)
  , ("data Stream(a) = (a Fn⟨• =Recursive> Stream(a)⟩)\nStream",
        "a0 Fn⟨• =Recursive> Stream(a0)⟩ ⇒ Stream(a0)")
  , ("data S2(a) = (a Fn⟨• =Recursive IO> S2(a)⟩)\nS2",
        "a0 Fn⟨• =IO Recursive> S2(a0)⟩ ⇒ S2(a0)")
    -- pack: list introduction from a bundle — (elements ; pack) replaces
    -- the list(…) special form; elements are full programs, groups delimit
  , ("(1 2 3 >> pack)",          "• ⇒ List(Int)")
  , ("(pack)",                   "a0ⁿ⁰ ⇒ List(a0)")   -- final position: open
  , ("(1 \"a\" 2 \"b\" >> pack2)", "• ⇒ List(Box(Int Str))")
    -- exponent syntax in type declarations: literal ^k (and Unicode
    -- superscript input) expands to k copies; segments repeat wholesale
  , ("type T3 = (Int^3 | Str)\n1 2 3 >> alt1 >> (pass | drop >> \"x\")", "• ⇒ T3")
  , ("type W = (• | Int³)\n1 2 3 >> alt2 >> (forget | pass)", "• ⇒ W")
  , ("type PP = ((Int Str)^2 | •)\n1 \"a\" 2 \"b\" >> alt1 >> (pass | forget)", "• ⇒ PP")
    -- foldExp: the exponent eliminator — variadic folds over bare stack
    -- products; n is erased and generalizes per def
  , ("[+] 0 ... >> foldExp",                    "Intⁿ⁰ ⇒ Int")
  , ("def total = [+] 0 ... >> foldExp\ntotal", "Intⁿ⁰ ⇒ Int")
    -- GLA generators: width-polymorphic wiring over bundles
  , ("dupN",   "a0ⁿ⁰ ⇒ a0ⁿ⁰ a0ⁿ⁰")
  , ("addN",   "Intⁿ⁰ Intⁿ⁰ ⇒ Intⁿ⁰")
  , ("zipN",   "a0ⁿ⁰ a1ⁿ⁰ ⇒ (a0 a1)ⁿ⁰")
  , ("sumN",   "Intⁿ⁰ ⇒ Int")
  , ("firstTrue", "Fn⟨• ⇒ ρ0⟩ ((• | •) Fn⟨• ⇒ ρ0⟩)ⁿ⁰ ⇒ ρ0")
    -- (before the grouped-compound constraint fix this leaked fake
    -- polymorphism: a0ⁿ a1ⁿ ⇒ Int, crashing on non-Int bundles)
  , ("def dot = zipN >> [(acc a b -> (a b >> *) acc >> +)] 0 ... >> foldExp2\ndot", "Intⁿ⁰ Intⁿ⁰ ⇒ Int")
    -- two-tier control flow: p? routes and keeps, bare p forgets to Bool
  , ("equals",                                  "a0 a0 ⇒ Bool")
  , ("less",                                    "Int Int ⇒ Bool")
  , ("odd",                                     "Int ⇒ Bool")
  , ("equals?",                                 "a0 a0 ⇒ (a0 | a0)")
    -- recursive type declarations: nominal, Name rolls / Name? unrolls
    -- Nat is declared ZERO-first, and Maybe is now PAYLOAD-first,
    -- so the printer no longer folds this — the iso Nat ≅ 1 + Nat
    -- still holds, but Braid's sums are rigid: order is semantic.
  , ("type Nat = (• | Nat)\nunNat",              "Nat ⇒ (• | Nat)")
  , ("type Nat = (• | Nat)\nNat",               "(• | Nat) ⇒ Nat")
  , ("type Tree(a) = (a | Tree(a) Tree(a))\nunTree", "Tree(a0) ⇒ (a0 | Tree(a0) Tree(a0))")
    -- data keyword: nominal without recursion; single-alternative
    -- bodies get doors against the field stack
  , ("data Person = (Str Int)\nPerson",         "Str Int ⇒ Person")
  , ("data Person = (Str Int)\nunPerson",       "Person ⇒ Str Int")
  , ("data Flag = (• | •)\nunFlag",             "Flag ⇒ Bool")
    -- generated folds: definition by points (recursive slots pre-folded)
  , ("type Nat = (• | Nat)\nfoldNat", "Fn⟨• ⇒ ρ0⟩ Fn⟨ρ0 ⇒ ρ0⟩ Nat ⇒ ρ0")
    -- List is now a declared type in the prelude; the library is derived
  , ("uncons",  "List(a0) ⇒ (• | a0 List(a0))")
  , ("cons",    "a0 List(a0) ⇒ List(a0)")
    -- stack-kinded parameters: zip without Pair
  , ("zip",     "List(a0) List(a1) =Recursive> List(Box(a0 a1))")
    -- ...and its inverse, plus the indexed read (2026-09-14): the two
    -- list words `examples/frame.braid` found missing
  , ("unzip",   "List(Box(a0 a1)) =Recursive> List(a0) List(a1)")
  , ("nth",     "Int List(a0) =Recursive> Maybe(a0)")
    -- the two string prims the CSV loader needed
  , ("split",   "Str Str ⇒ List(Str)")
  , ("asFloat?", "Str ⇒ (Float | Str)")
  , ("mapN2",   "Fn⟨a0 a1 ⇒ a2⟩ (a0 a1)ⁿ⁰ ⇒ a2ⁿ⁰")
    -- STRENGTH as an ordinary word: run a program one wire deeper.
    -- Composing it once per context wire is exactly what threads a
    -- resource past a pure stage, which is why stage 4 needs no new
    -- machinery for the pure case.
  , ("lift",                          "Fn⟨ρ0 ⇒ ρ1⟩ ⇒ Fn⟨a0 ρ0 ⇒ a0 ρ1⟩")
  , ("[dup >> *] >> lift",            "• ⇒ Fn⟨a0 Int ⇒ a0 Int⟩")
  , ("[dup >> *] >> lift >> lift",    "• ⇒ Fn⟨a0 a1 Int ⇒ a0 a1 Int⟩")
    -- INDICES: Fin(n) with witnessed introductions.  Every intro's n
    -- is forced by an input — a live bundle, or a literal's offset.
    -- EFFECTS: the io grade.  Five prims are marked; everything else
    -- infers.  A pure arrow prints exactly as it always did.
  , ("print",     "a0 =IO> •")
  , ("readLine",  "• =IO> (Str | Str)")
  , ("readFile",  "Str =IO> (Str | Str)")
  , ("evalAs",    "Fn⟨ρ0 ⇒ ρ1⟩ Code ρ0 ⇒ (ρ1 | Str ρ0)")
    -- `box` defers the RUN, and that costs the result's TYPE: what the
    -- boxed code returns is discovered when it runs, so the hit track is
    -- an existential its callers must stay parametric in
  , ("box",       "Fn⟨ρ0 ⇒ ρ1⟩ Code ⇒ Fn⟨ρ0 ⇒ (ρ1 | Str ρ0)⟩")
    -- pushing an action is PURE; the effect lives inside the Fn, and
    -- `ev` is where it transfers back out
  , ("[print]",   "• ⇒ Fn⟨a0 =IO> •⟩")
  , ("[print] 5 >> ev", "• =IO> •")
  , ("[dup >> *] 5 >> ev", "• ⇒ Int")
    -- reflect READS a program without running it: pure, any grade
  , ("reflect",   "Fn⟨ρ0 ⇒ ρ1⟩ ⇒ (Code | Str)")
    -- STAGE 5e: RECURSION IS A MARKER.  `use Recursive` puts the def's
    -- own name in scope in its own body; elaboration rewrites the body
    -- to the closed form before inference, so the def is still a closed
    -- spine and the label is the scope's receipt.
  , ("def decr = _ 1 >> -\n\
     \def fac = use Recursive ; (n -> n >> zero? >> ((z -> 1) | (m -> m (m >> decr >> fac) >> *)) >> merge)\n\
     \fac", "Int =Recursive> Int")
    -- point-free: the name is a word, so a body with no binder works
  , ("def lt100? = _ 100 >> lt? >> (_ drop | _ drop)\n\
     \def double = 2 _ >> *\n\
     \def until100 = use Recursive ; lt100? >> (double >> until100 | _) >> merge\n\
     \until100", "Int =Recursive> Int")
    -- a binder parameter of the def's own name SHADOWS it, as it
    -- shadows any word — and the receipt is still minted, because a
    -- receipt says what the SCOPE did, not what the body happened to
  , ("def f = use Recursive ; (f -> f 1 >> +)\nf", "Int =Recursive> Int")
    -- a self-call inside a quotation is a CAPTURE, and abstraction
    -- elimination handles it: guarded corecursion, unchanged
  , ("data Stream(a) = (a Fn⟨• =Recursive> Stream(a)⟩)\n\
     \def from = use Recursive ; (n -> n [n 1 >> + >> from] >> Stream)\n\
     \from", "Int =Recursive> Stream(Int)")
    -- the label is a SET: a marked def that also calls `loop` says it
    -- once
  , ("def spin = use Recursive ; [done] ... >> loop\nspin", "ρ0 =Recursive> ρ0")
    -- the marker is INNERMOST, so a functor on the same header sees the
    -- closed spine rather than a name that is not in scope yet
  , ("def idF = (c -> c)\nfunctor Same = idF\n\
     \def down = use Same Recursive ; (n -> n >> zero? >> ((z -> 0) | (m -> m >> _ 1 >> - >> down)) >> merge)\n\
     \down", "Int =Recursive Same> Int")
    -- `fix` is DERIVED now (it left the prim set 2026-09-14): the body
    -- takes the knot DEEPEST and then its own arguments, and `fix`
    -- hands back the knotted Fn.  Its own arrow carries the label the
    -- scope it is written under minted.
  , ("fix", "Fn⟨Fn⟨ρ0 =Recursive> ρ1⟩ ρ0 ⇒ ρ1⟩ =Recursive> Fn⟨ρ0 =Recursive> ρ1⟩")
    -- the label sits on the knot it hands out and on the self it hands
    -- in.  The body is asked for no grade of its own.
    -- GRADES JOIN (5a⁹⁄₁₀).  A derived higher-order word does not
    -- narrow its arguments: `while` runs a test and a body and may
    -- recurse, so IT carries `Recursive` — but neither quotation is asked
    -- for it, and a written pure `Fn` reaches both.
  , ("while",  "Fn⟨ρ0 ⇒ (ρ1 | ρ2)⟩ Fn⟨ρ1 ⇒ ρ0⟩ ρ0 =Recursive> ρ2")
  , ("until",  "Fn⟨ρ0 ⇒ (ρ1 | ρ2)⟩ Fn⟨ρ2 ⇒ ρ0⟩ ρ0 =Recursive> ρ1")
    -- the join is a JOIN, not a unification: an io body makes the loop
    -- io as well as Recursive, and the labels sort
  , ("[[dup >> print ...] ... >> ev >> done] ... >> loop", "a0 =IO Recursive> a0")
    -- and a derived word that runs its argument and then prints does
    -- not demand IO OF the argument (the `logged` case from the plan)
  , ("(f -> f ... >> ev >> \"done\" ... >> print ...)",
     "Fn⟨• ⇒ ρ0⟩ =IO> ρ0")
    -- two `Fn` rows each carrying a label the other lacks still UNIFY
    -- (they are the same row, not two parts of a composition): that is
    -- `unifyEff`'s bridge, which composition no longer reaches
  , ("def spin = [done] ... >> loop\ndef yell = \"a\" >> print\n[yell] [spin] >> eq? >> (drop drop | drop drop) >> merge",
     "• ⇒ •")
    -- three labels from three sources still UNION on one arrow: the
    -- join is the whole point, and the set displays sorted
  , ("def tracer = (c -> c)\nfunctor Traced = tracer\ndef fac = [(self n -> n >> zero? >> ((z -> 1) | (m -> m (m 1 >> - >> self ... >> ev) >> *)) >> merge)] ... >> fix ... >> ev\ndef report = use Traced ; fac ; toStr ; print\nreport",
     "Int =IO Recursive Traced> •")
    -- structural recursors mint NOTHING: they are bounded by the value
    -- they eat, so the whole derived library stays unlabelled
  , ("foldList", "Fn⟨• ⇒ a0⟩ Fn⟨a0 a1 ⇒ a0⟩ List(a1) ⇒ a0")
  , ("fold",   "Fn⟨a0 a1 ⇒ a0⟩ a0 List(a1) ⇒ a0")
  , ("map",    "Fn⟨a0 ⇒ a1⟩ List(a0) ⇒ List(a1)")
  , ("filter", "Fn⟨a0 ⇒ (a1 | a2)⟩ List(a0) ⇒ List(a1)")
  , ("reverse", "List(a0) ⇒ List(a0)")
    -- absorption: a recursive word beside a pure one is Recursive, not an
    -- error — the union is what composition computes
  , ("def fac = [(self n -> n >> zero? >> ((z -> 1) | (m -> m (m 1 >> - >> self ... >> ev) >> *)) >> merge)] ... >> fix ... >> ev\ndef twice = fac >> dup >> +\ntwice", "Int =Recursive> Int")
    -- and the union with IO sorts: labels are a SET, displayed in order
  , ("def fac = [(self n -> n >> zero? >> ((z -> 1) | (m -> m (m 1 >> - >> self ... >> ev) >> *)) >> merge)] ... >> fix ... >> ev\ndef shout = fac >> toStr >> print\nshout", "Int =IO Recursive> •")
    -- a WRITTEN `=Recursive>` takes recursive code AND pure code (the pure
    -- quotation's row is open, so it absorbs the label)
  , ("data Step = (Fn⟨Int =Recursive> Int⟩)\ndef fac = [(self n -> n >> zero? >> ((z -> 1) | (m -> m (m 1 >> - >> self ... >> ev) >> *)) >> merge)] ... >> fix ... >> ev\n[fac] >> Step", "• ⇒ Step")
  , ("data Step = (Fn⟨Int =Recursive> Int⟩)\n[dup >> *] >> Step", "• ⇒ Step")
    -- a def built with fix keeps the arity its binder gives it
  , ("def fac = [(self n -> n >> zero? >> ((z -> 1) | (m -> m (m 1 >> - >> self ... >> ev) >> *)) >> merge)] ... >> fix ... >> ev\nfac", "Int =Recursive> Int")
    -- the generated STRUCTURAL RECURSOR is a builtin now, and its
    -- scheme is derived from the declaration rather than inferred from
    -- generated source.  Four shapes pin the derivation: a recursive
    -- slot sharing its alternative (the result is then one wire), a
    -- recursive slot that is its alternative's only slot (the result
    -- may be a whole stack), a payload-free alternative, and an
    -- alternative that is a bare stack parameter.
  , ("foldList", "Fn⟨• ⇒ a0⟩ Fn⟨a0 a1 ⇒ a0⟩ List(a1) ⇒ a0")
  , ("type Tree(a) = (a | Tree(a) Tree(a))\nfoldTree", "Fn⟨a0 ⇒ a1⟩ Fn⟨a1 a1 ⇒ a1⟩ Tree(a0) ⇒ a1")
  , ("type Nat = (• | Nat)\nfoldNat", "Fn⟨• ⇒ ρ0⟩ Fn⟨ρ0 ⇒ ρ0⟩ Nat ⇒ ρ0")
  , ("foldBox", "Fn⟨ρ0 ⇒ ρ1⟩ Box(ρ0) ⇒ ρ1")
    -- composition propagates
  , ("1 >> print", "• =IO> •")
  , ("dup >> *",   "Int ⇒ Int")        -- and pure stays bare
    -- several effectful atoms in one stage are legal and run
    -- left-to-right (deepest first) — design-effects.md's decree
  , ("print print", "a0 a1 =IO> •")
  , ("at",        "Fin(n0) a0ⁿ⁰ ⇒ a0")
  , ("indicesN",  "a0ⁿ⁰ ⇒ (Fin(n0) a0)ⁿ⁰")
  , ("checkedAt", "Int a0ⁿ⁰ ⇒ (Fin(n0) a0ⁿ⁰ | Int a0ⁿ⁰)")
  , ("weaken",    "Fin(n0) ⇒ Fin(n0+1)")
  , ("finInt",    "Fin(n0) ⇒ Int")
    -- the literal family: finK's bound is k+1+n, so the offset IS the
    -- proof that k is in range, and `weaken` keeps it true
  , ("fin0",              "• ⇒ Fin(n0+1)")
  , ("fin2",              "• ⇒ Fin(n0+3)")
  , ("fin2 >> weaken",    "• ⇒ Fin(n0+4)")
    -- the bound is the LIVE width, correlated by the checker
  , ("1 2 3 >> indicesN", "• ⇒ Fin(3) Int Fin(3) Int Fin(3) Int")
  , ("1 10 20 30 >> checkedAt", "• ⇒ (Fin(3) Int Int Int | Int Int Int Int)")
  , ("1 10 20 30 >> checkedAt >> (at | drop drop drop drop)", "• ⇒ Maybe(Int)")
    -- non-final closes the width to 0, so `at` gets Fin(0): the
    -- uninhabited index, i.e. that branch can never run
  , ("at _",       "Fin(0) a0 ⇒ a1 a0")
  , ("indicesN _", "a0 ⇒ a0")
    -- a NON-FINAL open-width word closes to its zero-width case
    -- (n := 0), exactly as ρ-words close to ρ := • — one policy, both
    -- sorts.  This never worked before: substOnce rebuilt the closed
    -- exponent with the raw constructor, and the leftover zero-copy
    -- node tripped the recursive-call placement check.
  , ("sumN _",  "a0 ⇒ Int a0")   -- the seed, beside the wire
  , ("forget _", "a0 ⇒ a0")      -- the ρ analogue, for comparison
  , ("unzipN",  "(a0 a1)ⁿ⁰ ⇒ a0ⁿ⁰ a1ⁿ⁰")
  , ("map",     "Fn⟨a0 ⇒ a1⟩ List(a0) ⇒ List(a1)")
  , ("fold",    "Fn⟨a0 a1 ⇒ a0⟩ a0 List(a1) ⇒ a0")
  , ("def square = dup >> *\nsquare >> square", "Int ⇒ Int")
  , ("def first = id drop\n1 2 >> first",       "• ⇒ Int")
    -- one def used at two different types = let-polymorphism
  , ("def discard = drop\n1 discard >> true discard", "a0 ⇒ Bool")
    -- recursive defs (monomorphic self-reference)
  , ("def decr = _ 1 >> -\ndef lt2? = _ 2 >> lt? >> (_ drop | _ drop)\ndef fib = [(self ... -> lt2? >> (_ | (n -> n >> decr >> self ... >> ev >> _ (n 2 >> - >> self ... >> ev) >> +)) >> merge)] ... >> fix ... >> ev\nfib", "Int =Recursive> Int")
    -- a def body may leave a bracket open: the lines that close it
    -- belong to the body, so a blank line does not end the block and a
    -- `def`-looking line inside the bracket is code, not a declaration
    -- WIDTH parameters (a third kind, declared by use under `^`) —
    -- and they display-fold, which needed matchAlias to learn SExp
  , ("type Mat(n, m) = Fn⟨Int^n ⇒ Int^m⟩\n[dupN >> addN]",
     "• ⇒ Mat(n0, n0)")
  , ("type Mat(n, m) = Fn⟨Int^n ⇒ Int^m⟩\ntype Sq(n) = Mat(n, n)\n[dupN >> addN]",
     "• ⇒ Sq(n0)")
    -- a stack-shaped RHS: `^` lives in the stack parser, so the body
    -- must be parsed as a stack (this used to be "Unexpected tokens")
  , ("type T = Int^3\ntype U = (T | Str)\nnil",  "• ⇒ List(a0)")
    -- KINDED type parameters: a bare name is one wire, `...` is a
    -- stack.  The polymorphic pair was inexpressible while every
    -- parameter was stack-kinded (the split was ambiguous).
    -- RESOURCES (design-effects stage 2): a nominal threaded wire,
    -- folding onto the ARROW as `=Name>` when it rides a suffix.
  , ("resource Log = Str\ndef note = unLog _ >> cat >> Log\nnote",
     "Str =Log> •")
    -- bottom-anchored routing is width-polymorphic: the resource stays
    -- put and the remainder threads, which is what lets the elaborator
    -- place wires without consulting inference
  , ("resource Log = Str\ndef note = (unLog _ >> cat >> Log) ...\nnote",
     "Str ρ0 =Log> ρ0")
  , ("resource Counter = Int\ndef bump = unCounter >> 1 ... >> + >> Counter\ndef tick = _ bump ...\ntick",
     "a0 Counter ρ0 ⇒ a0 Counter ρ0")
    -- the grade and the resources are the same arrow: one `=IO Log>`
  , ("resource Log = Str\ndef peek = unLog >> dup >> print ... >> Log\npeek",
     "• =IO Log> •")
  , ("resource Log = Str\ndef quiet = unLog >> dup >> drop ... >> Log\nquiet",
     "• =Log> •")
    -- NOMINAL, which is the whole point: a bare Int Int is never a
    -- resource, so nothing folds by accident
  , ("resource GameState = Int Int\ndef notState = swap\nnotState",
     "a0 a1 ⇒ a1 a0")
    -- the roll/unroll doors do not fold (no suffix on the input side)
  , ("resource Log = Str\nLog",   "Str ⇒ Log")
  , ("resource Log = Str\nunLog", "Log ⇒ Str")
    -- STAGE 4: `use` opens an ambient scope and the elaborator writes
    -- every `_`/`...` — the body below contains none.
  , ("resource Log = Str\nresource Counter = Int\ndef bump = unCounter >> 1 ... >> + >> Counter\ndef f = use Log Counter >> dup >> * >> bump\nf",
     "Int ρ0 =Log Counter> Int ρ0")
  , ("resource Log = Str\nresource Counter = Int\ndef note = unLog _ >> cat >> Log\ndef f = use Log Counter >> \"x\" >> note\nf",
     "ρ0 =Log Counter> ρ0")
    -- `use` ASSERTS its claim: the wires must really be those resources,
    -- even when the body never touches one
  , ("resource Log = Str\ndef f = use Log >> dup\nf",
     "a0 ρ0 =Log> a0 a0 ρ0")
    -- `use` scopes COMPOSE.  A word threading exactly the scope's
    -- resources is already shaped like the stack, so it needs no
    -- routing and is callable from a scope over the same resources.
    -- Without this, a multi-resource word could be WRITTEN with `use`
    -- and then never CALLED from one, which makes the scope a notation
    -- rather than an abstraction.
  , ("resource Log = Str\nresource Counter = Int\ndef bump = unCounter >> 1 ... >> + >> Counter\ndef note = unLog _ >> cat >> Log\ndef step = use Log Counter >> toStr >> note >> bump\ndef twice = use Log Counter >> step >> step\ntwice",
     "a0 a1 ρ0 =Log Counter> ρ0")
    -- ... and a resourceful step is exactly a fold's step function, so
    -- folding it over data is the ordinary `fold`
  , ("resource Books = Str\ndef say = unBooks _ >> cat >> Books\ndef step = use Books >> toStr >> say\n[step]",
     "• ⇒ Fn⟨a0 ρ0 =Books> ρ0⟩")
    -- THEORIES (stage 3): named slots, models selected BY NAME with
    -- `use`, resolution as a renaming at elaboration.  Generic code is
    -- written once; only the scope differs.
  , ("theory Monoid(a) =\n    unit : • ⇒ a\n    op   : a a ⇒ a\nmodel IntSum : Monoid(Int) =\n    unit = 0\n    op   = +\ndef total = use IntSum ; [op] unit ... ; foldExp\ntotal",
     "Intⁿ⁰ =IntSum> Int")
    -- a model's carrier is a full type EXPRESSION, not a bare name.
    -- Every structure worth having a theory of is parameterized, so
    -- scraping identifiers out of the head read `T(List(Int))` as two
    -- arguments and rejected it.
  , ("theory Wrap(a) =\n    wrap : a ⇒ a\nmodel L : Wrap(List(Int)) =\n    wrap = id\ndef w = use L ; wrap\nw",
     "List(Int) =L> List(Int)")
  , ("theory Wrap(a) =\n    wrap : a ⇒ a\nmodel F : Wrap(Fn⟨Int ⇒ Int⟩) =\n    wrap = id\ndef w = use F ; wrap\nw",
     "Fn⟨Int ⇒ Int⟩ =F> Fn⟨Int ⇒ Int⟩")
    -- a slot body may call the module's OWN defs: a theory declaration
    -- is a signature, so slots are forward-declared and the two
    -- directions (def calls slot, slot calls def) both work
  , ("theory Monoid(a) =\n    unit : • ⇒ a\n    op   : a a ⇒ a\ndef myAdd = +\nmodel S : Monoid(Int) =\n    unit = 0\n    op   = myAdd\ndef total = use S ; [op] unit ... ; foldExp\ntotal",
     "Intⁿ⁰ =S> Int")
    -- STAGE 5a, item 0: SLOT-LOCAL VARIABLES.  A slot may name variables
    -- the theory does not declare, and is generalized over its own —
    -- `box : b ⇒ a` under `theory Wrap(a)` is `∀b. b ⇒ a`.  Nothing in
    -- the checker changed: `declaredSlots` already generalized the slot
    -- and `checkInstance` already compared bodies by subsumption.
  , ("theory Wrap(a) =\n    box : b ⇒ a\nmodel W : Wrap(Str) =\n    box = toStr\ndef w = use W ; box\nw",
     "a0 =W> Str")
    -- a `...` in a slot of a theory with no stack parameter is a
    -- slot-local STACK, so a theory can ask for `∀ρ. ρ ⇒ ρ`
  , ("theory Endo =\n    around : ... ⇒ ...\nmodel E : Endo =\n    around = ...\ndef a2 = use E ; around\na2",
     "ρ0 =E> ρ0")
    -- STAGE 5a, item 1: CONSTRUCTOR PARAMETERS.  `k` is written with its
    -- arity visible (`k(_, _)`), applied in the slots, and substituted
    -- away at the model — so what comes out is an ordinary type and
    -- inference never meets a constructor variable.
  , ("data K(a, b) = Fn⟨a ⇒ b⟩\ntheory Arrow(k(_, _)) over Doctrine =\n    embed   : Fn⟨a ⇒ b⟩ ⇒ k(a, b)\n    compose : k(a, b) k(b, c) ⇒ k(a, c)\nmodel P : Arrow(K) =\n    embed  = K\n    compose = (f g -> [(x -> f ; unK ; _ x ; ev ; (y -> g ; unK ; _ y ; ev))] ; K)\ndef t = over P ; compose\nt",
     "K(a0, a1) K(a1, a2) ⇒ K(a0, a2)")
    -- the substitution reaches inside an Fn type in a slot too
  , ("data K(a, b) = Fn⟨a ⇒ b⟩\ntheory Arrow(k(_, _)) over Doctrine =\n    embed   : Fn⟨a ⇒ b⟩ ⇒ k(a, b)\n    compose : k(a, b) k(b, c) ⇒ k(a, c)\nmodel P : Arrow(K) =\n    embed  = K\n    compose = (f g -> [(x -> f ; unK ; _ x ; ev ; (y -> g ; unK ; _ y ; ev))] ; K)\ndef ar = over P ; embed\nar",
     "Fn⟨a0 ⇒ a1⟩ ⇒ K(a0, a1)")
  , ("theory Monoid(a) =\n    unit : • ⇒ a\n    op   : a a ⇒ a\nmodel StrCat : Monoid(Str) =\n    unit = \"\"\n    op   = cat\ndef joined = use StrCat ; [op] unit ... ; foldExp\njoined",
     "Strⁿ⁰ =StrCat> Str")
    -- the grade is inferred through defs, not read off a name
  , ("def shout = toStr >> print\nshout",          "a0 =IO> •")
  , ("def quiet = toStr >> drop\nquiet",           "a0 ⇒ •")
  , ("def p = print\ndef q = p\nq",               "a0 =IO> •")
    -- ε-polymorphism: one `map`, both readings, no annotation
  , ("[toStr] (1 2 3 >> pack) >> map",             "• ⇒ List(Str)")
  , ("def logAll = [dup >> print ...] ... >> map\nlogAll", "List(a0) =IO> List(a0)")
  , ("data Pair(a, b) = (a b)\nPair",     "a0 a1 ⇒ Pair(a0, a1)")
  , ("data Pair(a, b) = (a b)\nunPair",   "Pair(a0, a1) ⇒ a0 a1")
    -- `...` takes a whole stack into ONE wire: how multi-wire
    -- aggregates survive single-wire list cells
  , ("data B(...) = (...)\nB",            "ρ0 ⇒ B(ρ0)")
  , ("data B(...) = (...)\nunB",          "B(ρ0) ⇒ ρ0")
  , ("data T(t, ...) = (t ...)\nT",       "a0 ρ0 ⇒ T(a0, ρ0)")
    -- list cells are one wire, so `List` needs no splice: its parameter
    -- is forced to a wire because it sits BEFORE the recursive slot
  , ("def spanning = (1\n\n2 ... >> +\n)\nspanning",   "• ⇒ Int")
  , ("def blk =\n    (1\n\n     2 ... >> +\n     )\nblk",  "• ⇒ Int")
    -- the naming binder inside a def: names reach the rest of the body,
    -- and the binder does not close the stack — the open-arity `sumN`
    -- still sees whatever else was passing through
  , ("def tagged =\n    -> h m f\n    sumN\n    h ... >> +\ntagged",
     "Int Int Int Intⁿ⁰ ⇒ Int")
    -- STAGE 4½: PROVENANCE.  `use F` mints F onto everything it
    -- elaborated, and the manifest carries it to every caller.
  , (idF ++ "def p = use Same >> dup >> *\np",          "Int =Same> Int")
  , (idF ++ "def p = use Same >> dup >> *\ndef q = p >> p\nq",
     "Int =Same> Int")
    -- labels are a SET: two functors union, io is one member among
    -- them, and a resource name joins them in the same manifest
  , (idF ++ "def idG = (c -> c)\nfunctor Twice = idG\n"
         ++ "def p = use Same Twice >> dup >> *\np", "Int =Same Twice> Int")
  , (idF ++ "def p = use Same >> dup >> * >> print\np", "Int =IO Same> •")
  , (idF ++ "resource Fuel = Int\ndef p =\n    use Fuel Same\n    dup >> *\np",
     "Int ρ0 =Same Fuel> Int ρ0")
    -- a labelled word composes with an unlabelled one and with an io
    -- one: unification absorbs into the open tail, exactly as io always
    -- did.  Nothing about `=Same>` makes a word less composable.
  , (idF ++ "def p = use Same >> dup >> *\ndef q = p >> toStr >> print\nq",
     "Int =IO Same> •")
    -- two DIFFERENT labels meeting at a cut: neither tail is poorer, so
    -- the rows bridge through a shared residual
  , (idF ++ "def idG = (c -> c)\nfunctor Twice = idG\n"
         ++ "def p = use Same >> dup >> *\ndef q = use Twice >> _ 1 >> +\n"
         ++ "def both = p >> q\nboth", "Int =Same Twice> Int")
    -- a functor's own word is UNLABELLED — it is called at elaboration,
    -- not elaborated under anything
  , (idF ++ "idF", "a0 ⇒ a0")
    -- STAGE 5a½: `Recursive` joins that same set.  A receipt, io and
    -- recursion union in one manifest and display sorted.
  , (idF ++ "def q = use Same >> [_ 100 >> less?] [2 _ >> *] ... >> while\nq",
     "Int =Recursive Same> Int")
  , (idF ++ "def p = use Same >> [_ 100 >> less?] [2 _ >> *] ... >> while >> toStr >> print\np",
     "Int =IO Recursive Same> •")
    -- TEMPLATES: one body, two instantiations, two PRINCIPAL types.
    -- Nothing is dispatched and nothing is passed; the expansion is
    -- re-inferred where it lands, so there is no rank-1 wall.
  , (tmplMod ++ "use IntSum ; fold1", "Intⁿ⁰ =IntSum> Int")
  , (tmplMod ++ "use StrCat ; fold1", "Strⁿ⁰ =StrCat> Str")
    -- a template calling a template: the instantiating scope
    -- instantiates the whole chain
  , (tmplMod ++ "use IntSum ; quad", "Int =IntSum> Int")
  , (tmplMod ++ "use StrCat ; quad", "Str =StrCat> Str")
    -- through a def, and nested scopes resolve innermost-first — and
    -- BOTH scopes are on the receipt, because both were entered
  , (tmplMod ++ "def a = use IntSum ; twice\ndef b = use StrCat ; twice\n\
     \def c = use IntSum ; use StrCat ; twice\nc", "Str =IntSum StrCat> Str")
    -- the handler: an effectful arrow is a resource + a macro + a
    -- theory, and this is the macro half.  `=Log>` is discharged.
  , (handlerMod ++ "collectLog", "Fn⟨ρ0 =Log> ρ1⟩ ⇒ Fn⟨ρ0 ⇒ Str ρ1⟩")
    -- and generically: a template over a theory naming the two words a
    -- handler needs, at two different resources
  , (collectorMod ++ "use Logs ; collected",
     "Fn⟨ρ0 =Log> ρ1⟩ =Logs> Fn⟨ρ0 ⇒ Str ρ1⟩")
  , (collectorMod ++ "use Counts ; collected",
     "Fn⟨ρ0 =Counter> ρ1⟩ =Counts> Fn⟨ρ0 ⇒ Int ρ1⟩")
    -- TRANSPORT (5c, 5c½).  THE DISPLAY FOLD: at the base a word of a
    -- category is `• ⇒ Arr(Int, Int)` carrying `Funcs`, and a carrier
    -- the label owns folds onto the glyph exactly as a threaded
    -- resource does.
  , (modeMod ++ "chain", "Int =Funcs> Int")
    -- the fold wants EXACTLY ONE carrier, so two of them side by side
    -- print unfolded: honest, well-typed, and visibly not composition
    -- in the category, which is written under the marker.
  , (modeMod ++ "chain chain", "• =Funcs> Arr(Int, Int) Arr(Int, Int)")
    -- and under the marker it composes: a word of the category inside
    -- `use Funcs` is left alone and the `;` around it is the composition
  , (modeMod ++ "def two = use Funcs ; chain ; chain\ntwo", "Int =Funcs> Int")
    -- an ENTRY slot (`sample`: no carrier in, one carrier out) is
    -- already a stage of the category, so it is left alone too.  Its
    -- type said so in WRITING, which keeps this out of inference.
  , (modeMod ++ "def s2 = use Funcs ; sample ; sample\ns2", "Int =Funcs> Int")
    -- the receipt is an ordinary label: it unions with io by the same
    -- semilattice as everything else.  `over` mints nothing, so the
    -- only label here is the one `chain` already wore.
  , (modeMod ++ "def obs = over Funcs ; chain ; observe\nobs ; print",
     "• =Funcs IO> •")
    -- a sealed category: same fold, and no exit to fold back through
  , (sealedMod ++ "guarded", "Int =Sealed> Int")
    -- STAGE 5c½.  `over M` — a HAND-BUILT word of the category.  It
    -- applies nothing and so MINTS nothing: the def displays as the
    -- carrier it is, unfolded, because `=Funcs>` is provenance and this
    -- code did not go through the functor.  Membership is the carrier
    -- in the type plus the K-word table.
  , (modeMod ++ "def hand = [dup ; +] ; Arr\ndef byHand = over Funcs ; hand\nbyHand",
     "• ⇒ Arr(Int, Int)")
    -- and it composes under the marker like any other word of the
    -- category — THAT composite went through the functor, so it folds
  , (modeMod ++ "def hand = [dup ; +] ; Arr\ndef byHand = over Funcs ; hand\n\
     \def mix = use Funcs ; byHand ; add1\nmix", "Int =Funcs> Int")
    -- a base def that merely PRODUCES a carrier is not a word of the
    -- category, and its type is the same as `byHand`'s: the difference
    -- is the written header, never an inferred type.
  , (modeMod ++ "def hand = [dup ; +] ; Arr\nhand", "• ⇒ Arr(Int, Int)")
    -- LEVEL THREE: with a strength declared, a wider stage transports
    -- by being packed with the pairing the strength names
  , (wideMod ++ "def sq = use Wide ; dup ; *\nsq", "Int =Wide> Int")
    -- and a narrow stage is whiskered: `...` is what `first` becomes
  , (wideMod ++ "def w = use Wide ; dup ; add1 ... ; *\nw", "Int =Wide> Int")
    -- LEVEL ONE: composition alone.  `over` composes carriers built by
    -- hand, and the def is a word of the category like any other.
  , (halfMod ++ "def f = over HW ; [inc] ; H\ndef g = over HW ; f f ; compose\ng",
     "• ⇒ H(Int, Int)")
    -- `over T` is the template header; the def's own type is the
    -- instantiation's, and `over` leaves no receipt of its own here
    -- either — the `use IntSum` is what minted
  , (tmplMod ++ "use IntSum ; twice", "Int =IntSum> Int")
    -- STAGE 5c½: EVERY `use` MINTS.  A model of `Base` leaves its
    -- name on everything it renamed, exactly as a functor does.
  , ("def dupInt = dup >> _ _ 0 >> _ +\nmodel Opt : Base = dupInt = dup\n\
     \def p = use Opt ; dupInt ; +\np", "Int =Opt> Int")
    -- it recurses into quotations, and the receipt rides out with them
  , ("def twice = dup >> +\ndef double = 2 _ >> *\n\
     \model Opt : Base = twice = double\n\
     \def q = use Opt ; [twice] ... ; map\nq", "List(Int) =Opt> List(Int)")
    -- the generated word is an ordinary `Code ⇒ Code`, for `[Opt]`
  , ("def twice = dup >> +\ndef double = 2 _ >> *\n\
     \model Opt : Base = twice = double\nOpt", "Code ⇒ Code")
  ]

-- TEMPLATES (stage 5a).  A def whose `use` names a THEORY is a body
-- waiting for a model; a def whose `use` names a MODEL expands
-- it there, renames it there, and RE-INFERS it there — so every
-- instantiation has its own principal type.
tmplMod :: String
tmplMod =
  "theory Monoid(a) =\n\
  \    unit : • ⇒ a\n\
  \    op   : a a ⇒ a\n\
  \model IntSum : Monoid(Int) =\n\
  \    unit = 0\n\
  \    op   = +\n\
  \model StrCat : Monoid(Str) =\n\
  \    unit = \"\"\n\
  \    op   = cat\n\
  \def fold1 = over Monoid ; [op] unit ... ; foldExp\n\
  \def twice = over Monoid ; dup ; op\n\
  \def quad  = over Monoid ; twice ; twice\n"

-- the handler of stage 5a item 3: seed the resource, run the program,
-- unroll the wire — the arrow loses `=Log>` across it
handlerMod :: String
handlerMod =
  "resource Log = Str\n\
  \def note = unLog _ ; cat ; Log\n\
  \def collectLog = (f -> [f (\"\" ; Log) ... ; ev ; unLog ...])\n"

-- the GENERIC handler: a template is over a THEORY, never over a
-- resource name, so the two words a handler needs become slots
collectorMod :: String
collectorMod =
  "resource Log = Str\n\
  \resource Counter = Int\n\
  \theory Collector(e, a) =\n\
  \    seed   : • ⇒ e\n\
  \    unwrap : e ⇒ a\n\
  \model Logs : Collector(Log, Str) =\n\
  \    seed   = \"\" ; Log\n\
  \    unwrap = unLog\n\
  \model Counts : Collector(Counter, Int) =\n\
  \    seed   = 0 ; Counter\n\
  \    unwrap = unCounter\n\
  \def collected = over Collector ; (f -> [f (seed) ... ; ev ; unwrap ...])\n"

-- a trivial functor: the identity on Code.  Enough to ask what `use`
-- leaves behind, without a rewrite getting in the way.
idF :: String
idF = "def idF = (c -> c)\nfunctor Same = idF\n"

-- TRANSPORT (5c, reshaped in 5c\189).  A model whose theory has a
-- hom-object `k(_, _)` and slots at the composition and embedding
-- SHAPES is a label with a CARRIER: `use Funcs` sends every stage to
-- this model's embedding and every `;` to its composition.  No `mode`
-- line, and no slot NAME is read — `embed`/`compose` are this fixture's
-- taste.  `Arrow` here declares NO strength, which is what pins the
-- one-wire level.  The boring model is enough for the whole mechanism,
-- and unlike `Circuit` it is pure, so the expected arrows carry nothing
-- but the receipt.
modeMod :: String
modeMod = unlines
  [ "data Arr(a, b) = Fn⟨a ⇒ b⟩"
  , "theory Arrow(k(_, _)) over Doctrine ="
  , "    embed   : Fn⟨a ⇒ b⟩ ⇒ k(a, b)"
  , "    compose   : k(a, b) k(b, c) ⇒ k(a, c)"
  , "    observe : k(Int, Int) ⇒ Int"
  , "    sample  : • ⇒ k(Int, Int)"
  , "def thenA = (f g -> [(x -> f ; unArr ; _ x ; ev ; (y -> g ; unArr ; _ y ; ev))] ; Arr)"
  , "def runA  = (f x -> f ; unArr ; _ x ; ev)"
  , "model Funcs : Arrow(Arr) ="
  , "    embed    = Arr"
  , "    compose   = thenA"
  , "    observe = (f -> f 7 ; runA)"
  , "    sample  = [dup ; +] ; Arr"
  , "def add1 = _ 1 ; +"
  , "def dbl  = 2 _ ; *"
  , "def chain = use Funcs ; add1 ; dbl"
    -- a SECOND category over the same carrier, for the two-in-a-header
    -- and word-of-another-category refusals
  , "model Funcs2 : Arrow(Arr) ="
  , "    embed    = Arr"
  , "    compose   = thenA"
  , "    observe = (f -> f 7 ; runA)"
  , "    sample  = [dup ; +] ; Arr"
  ]

-- TRANSFORMATIONS (5d): two models of one theory, and a word between their
-- carriers.  `len` is opaque to the normalizer (it applies its handler,
-- and that `ev` has an open arrow), so every square here is decided at
-- the theory's samples \8212 which is why the samples correspond.
monoidMod :: String
monoidMod = unlines
  [ "theory Monoid(a) ="
  , "    unit   : \8226 \8658 a"
  , "    op     : a a \8658 a"
  , "    sample : \8226 \8658 a"
  , "model IntSum : Monoid(Int) ="
  , "    unit   = 0"
  , "    op     = +"
  , "    sample = 7"
  , "model ListMonoid : Monoid(List(Int)) ="
  , "    unit   = nil"
  , "    op     = append"
  , "    sample = 1 2 3 4 5 6 7 >> pack"
  , "def len = [(acc x -> acc >> _ 1 >> +)] 0 ... >> fold"
  ]

-- A CARRIER THAT HOLDS A FUNCTION (2026-09-14).  `K` is a value and a
-- linear map, exactly as `examples/autodiff.braid`'s `Rev` is, and the
-- two models build the SAME map out of different code (`d 3 >> *` and
-- `3 d >> *`).  The `sample` square is therefore not provable and goes
-- to the theory's evidence \8212 where it must be compared THROUGH the
-- exit, because `eq?` on a carrier holding a quotation is syntactic.
closureMod :: String
closureMod = unlines
  [ "data Two = Int Int"
  , "data K = Int Fn\10216Int \8658 Int\10217"
  , "theory Scale(a) ="
  , "    bump    : a \8658 a"
  , "    sample  : \8226 \8658 a"
  , "    observe : a \8658 Int"
  , "model Src : Scale(Two) ="
  , "    bump    = unTwo >> (v f -> (v 1 >> +) f >> Two)"
  , "    sample  = 2 3 >> Two"
  , "    observe = unTwo >> (v f -> v)"
  , "model Dst : Scale(K) ="
  , "    bump    = unK >> (v k -> (v 1 >> +) k >> K)"
  , "    sample  = 2 [(d -> 3 d >> *)] >> K"
  , "    observe = unK >> (v k -> v)"
  , "def toK = unTwo >> (v f -> v [(d -> d f >> *)] >> K)"
  ]

-- the same theory with NO exit: then there is nothing to observe the
-- carriers with, `eq?` weighs them directly, and the refusal says so
closureModNoExit :: String
closureModNoExit =
  unlines [ l | l <- lines closureMod, not ("observe" `isInfixOf` l) ]

-- SHAPE NO LONGER DETECTS (2026-09-13).  The same two arrows, declared
-- at the same signatures, WITHOUT `over Doctrine`: not a category, so
-- `use Plain` is the renaming it has always been and the spine comes
-- out untouched.  Membership is declared or it is not there.
plainMod :: String
plainMod = unlines
  [ "data Arr(a, b) = Fn\10216a \8658 b\10217"
  , "theory Shaped(k(_, _)) ="
  , "    embed   : Fn\10216a \8658 b\10217 \8658 k(a, b)"
  , "    compose : k(a, b) k(b, c) \8658 k(a, c)"
  , "def thenA = (f g -> [(x -> f ; unArr ; _ x ; ev ; (y -> g ; unArr ; _ y ; ev))] ; Arr)"
  , "model Plain : Shaped(Arr) ="
  , "    embed   = Arr"
  , "    compose = thenA"
  , "def add1 = _ 1 ; +"
  , "def dbl  = 2 _ ; *"
  ]

-- LEVEL ONE: composition and nothing else.  `over HW` composes carriers
-- built by hand; `use HW` has no embedding to transport a stage with.
halfMod :: String
halfMod = unlines
  [ "data H(a, b) = Fn\10216a \8658 b\10217"
  , "theory Half(k(_, _)) over Doctrine ="
  , "    compose : k(a, b) k(b, c) \8658 k(a, c)"
  , "def thenH = (f g -> [(x -> f ; unH ; _ x ; ev ; (y -> g ; unH ; _ y ; ev))] ; H)"
  , "model HW : Half(H) ="
  , "    compose = thenH"
  , "def inc = _ 1 ; +"
  , "def dbl = 2 _ ; *"
  ]

-- LEVEL THREE: composition, embedding AND a strength, so the elaborator
-- can pack a wide stage with the pairing the strength names (`P`) and
-- whisker a narrow one with `first`.
wideMod :: String
wideMod = unlines
  [ "data W(a, b) = Fn\10216a \8658 b\10217"
  , "data P(a, b) = a b"
  , "theory Wider(k(_, _)) over Doctrine ="
  , "    embed   : Fn\10216a \8658 b\10217 \8658 k(a, b)"
  , "    compose  : k(a, b) k(b, c) \8658 k(a, c)"
  , "    first : k(a, b) \8658 k(P(a, c), P(b, c))"
  , "    runW   : k(a, b) a \8658 b"
  , "def thenW = (f g -> [(x -> f ; unW ; _ x ; ev ; (y -> g ; unW ; _ y ; ev))] ; W)"
  , "def firstW = (f -> [(q -> q ; unP ; (x d -> f ; unW ; _ x ; ev ; (y -> y d ; P)))] ; W)"
  , "def runWi = (f x -> f ; unW ; _ x ; ev)"
  , "model Wide : Wider(W) ="
  , "    embed   = W"
  , "    compose  = thenW"
  , "    first = firstW"
  , "    runW   = runWi"
  , "def add1 = _ 1 ; +"
  , "def dbl  = 2 _ ; *"
  ]
-- a SEALED category: a theory with no eliminator, so nothing written in
-- the scope can leave it by any route the model offers
sealedMod :: String
sealedMod = unlines
  [ "data Cap(a, b) = Fn⟨a ⇒ b⟩"
  , "theory Vault(k(_, _)) over Doctrine ="
  , "    embed  : Fn⟨a ⇒ b⟩ ⇒ k(a, b)"
  , "    compose : k(a, b) k(b, c) ⇒ k(a, c)"
  , "def capThen = (f g -> [(x -> f ; unCap ; _ x ; ev ; (y -> g ; unCap ; _ y ; ev))] ; Cap)"
  , "model Sealed : Vault(Cap) ="
  , "    embed  = Cap"
  , "    compose = capThen"
  , "def inc = _ 1 ; +"
  , "def guarded = use Sealed ; inc ; inc"
  ]
-- (module source, expected print log, expected final stack rendering)
evalTests :: [(String, [String], String)]
evalTests =
    -- A FAMILY'S SLOT BODY NAMES THE PARAMETER'S SLOT (2026-09-15).
    -- `lit = (c -> (c ; lit) (0.0 ; lit) ; Dual)` — every theory name in
    -- a family's body is R's, the slot being defined included, so `lit`
    -- inside `lit` is Floats' `lit` and the body is unambiguous with no
    -- self-reference rule.  The zero tangent is `0.0 ; lit` and not a
    -- `zero` slot: the theory already names its zero, and `addUnit`
    -- already pins it.
  [ (famSrc ++ "def l = use Fwd(Floats) ; lit\n3.0 ; l ; unDual ; print ... ; print",
     ["3.0", "0.0"], "")
    -- SECOND DERIVATIVES, by applying the family to a member of itself.
    -- cube(x) = x\179 + 1, so cube''(2) = 6*2 = 12, and the file that
    -- wrote `cube` knows nothing about any of it.
  , (famSrc ++ "def dd = use Fwd(Fwd(Floats)) ; cube\n\
      \((2.0 1.0 ; Dual) (1.0 0.0 ; Dual) ; Dual) ; dd ; tangent ; tangent ; print",
     ["12.0"], "")
    -- A CONSTRUCTOR PARAMETER OF ARITY ONE (2026-09-15).  A theory
    -- parameter `f(_)` is what an exit whose RESULT varies by model
    -- wants when the result is itself parameterized — `report :
    -- k(Int, b) ⇒ d(b)` in `examples/prob.braid`.  `componentArrows`
    -- wrote TWO type arguments for every constructor parameter, on the
    -- assumption that one is always a hom-object, so a transformation
    -- over such a theory was refused with `Wrap(a0, a1) ⇒ Twice(a0,
    -- a1)`.  The arity is written in the declaration; it is read now.
  , ("data Wrap(a) = a\ndata Twice(a) = a a\n\
     \theory H(f(_)) =\n\
     \    sample  : \8226 \8658 f(Int)\n\
     \    bump    : f(Int) \8658 f(Int)\n\
     \    observe : f(Int) \8658 Int\n\
     \model One : H(Wrap) =\n\
     \    sample  = 7 ; Wrap\n\
     \    bump    = unWrap ; _ 1 ; + ; Wrap\n\
     \    observe = unWrap\n\
     \model Two : H(Twice) =\n\
     \    sample  = 7 7 ; Twice\n\
     \    bump    = unTwice ; (x y -> (x ; _ 1 ; +) (y ; _ 1 ; +)) ; Twice\n\
     \    observe = unTwice ; _ drop\n\
     \def widen = unWrap ; dup ; Twice\n\
     \transformation W : One \8658 Two = widen\n\
     \(7 ; Wrap) ; widen ; unTwice ; + ; print",
     ["14"], "")
    -- THE PARAMETERIZED EXIT (2026-09-14).  An exit whose result varies
    -- by model is a THEORY PARAMETER the model instantiates: `grad : a
    -- ⇒ g` is one slot with one type, and `g` is `Float` for the plain
    -- model and `Float` for the dual one here (a `Grad` in
    -- autodiff.braid).  A wire parameter used ONLY in an exit's output
    -- is instantiated per model and reaches nothing else.  The
    -- transformation then needs ONE COMPONENT PER PARAMETER, because
    -- the two ends of `grad`'s square sit at different ones.
  , ("data Dual = Float Float\n\
     \def zt = (d -> 0.0)\n\
     \def dadd = Dual(a, da) Dual(b, db) -> (a b ; fadd) (da db ; fadd) ; Dual\n\
     \def val = Dual(v, t) -> v\n\
     \def tan = Dual(v, t) -> t\n\
     \theory S(a, g) =\n\
     \    lit : Float \8658 a\n\
     \    add : a a \8658 a\n\
     \    sample : \8226 \8658 a\n\
     \    observe : a \8658 Float\n\
     \    grad : a \8658 g\n\
     \model F : S(Float, Float) =\n\
     \    lit = id\n\
     \    add = fadd\n\
     \    sample = 1.5\n\
     \    observe = id\n\
     \    grad = zt\n\
     \model D : S(Dual, Float) =\n\
     \    lit = (c -> c 0.0 ; Dual)\n\
     \    add = dadd\n\
     \    sample = 1.5 1.0 ; Dual\n\
     \    observe = val\n\
     \    grad = tan\n\
     \transformation V : D \8658 F = val, zt\n\
     \def p = over S ; (x -> x (2.0 ; lit) ; add)\n\
     \def pF = use F ; p\n\
     \def pD = use D ; p\n\
     \2.0 ; pF ; print\n\
     \(2.0 1.0 ; Dual) ; pD ; tan ; print",
     ["4.0", "1.0"], "")
    -- DESTRUCTURING BINDERS (2026-09-14).  A constructor pattern in a
    -- binder head is SYNTAX: it rewrites, before the parse tree exists,
    -- to the un-constructor stage a hand wrote until today.  All four
    -- forms — alone, mixed with a plain parameter, with the open `...`,
    -- and nested one deep.
  , ("data Dual = Float Float\ndata Wrap = Dual Int\n\
     \def dneg = Dual(a, da) -> (a ; fneg) (da ; fneg) ; Dual\n\
     \def mix = (Dual(a, da) x -> (a da ; fadd) x ; fadd)\n\
     \def open = (Dual(a, da) ... -> a da ; fadd)\n\
     \def deep = Wrap(Dual(a, da), n) -> (a da ; fadd) (n ; toFloat) ; fadd\n\
     \(1.0 2.0 ; Dual) ; dneg ; unDual ; print ... ; print\n\
     \(1.0 2.0 ; Dual) 4.0 ; mix ; print\n\
     \(1.0 2.0 ; Dual) ; open ; print\n\
     \((1.0 2.0 ; Dual) 3 ; Wrap) ; deep ; print",
     ["-1.0", "-2.0", "7.0", "3.0", "6.0"], "")
    -- `split` (2026-09-14): n+1 pieces for n occurrences, so the pieces
    -- and the separators rebuild the original — empty pieces included —
    -- and an empty separator cuts nothing.  `asFloat?` reads exactly
    -- the SOURCE notation for a Float literal, which is what the
    -- display prints, so `toStr ; asFloat?` is the identity.
  , ("(\"a,b,,c\" \",\" ; split) ; len ; print\n\
     \(\"a,b,,c\" \",\" ; split) ; printAll\n\
     \(\"x\" \"\" ; split) ; printAll\n\
     \(\"a--b\" \"--\" ; split) ; printAll",
     ["4", "a", "b", "", "c", "x", "a", "b"], "")
  , ("\"191.25\" ; asFloat? ; (print | print) ; merge\n\
     \\"-2.5\" ; asFloat? ; (print | print) ; merge\n\
     \\"1e-3\" ; asFloat? ; (print | print) ; merge\n\
     \\"100\" ; asFloat? ; (print | print) ; merge\n\
     \(0.1 0.2 ; fadd) ; toStr ; asFloat? ; (print | print) ; merge",
     ["191.25", "-2.5", "1e-3", "100", "0.30000000000000004"], "")
    -- `nth` and `unzip`, the two list words the frame found missing
  , ("def l3 = 1 (2 (3 nil ; cons) ; cons) ; cons\n\
     \0 l3 ; nth ; (print | \"none\" ; print) ; merge\n\
     \2 l3 ; nth ; (print | \"none\" ; print) ; merge\n\
     \5 l3 ; nth ; (print | \"none\" ; print) ; merge\n\
     \((1 \"a\" ; Box) ((2 \"b\" ; Box) nil ; cons) ; cons) ; unzip \n\
     \; (as bs -> as ; printAll ; bs ; printAll)",
     ["1", "3", "none", "1", "2", "a", "b"], "")
    -- NAMED FIELDS (2026-09-14).  A single-alternative `data` may name
    -- its positions, and each name becomes a PROJECTION WORD generated
    -- beside `unTrade` and `foldTrade`.  The type stays positional, so
    -- the roll, the unroll and the destructuring binder are untouched —
    -- which is what the last two lines check.
  , ("data Trade = (sym: Str, px: Float, qty: Int)\n\
     \def t = \"AAPL\" 191.25 100 ; Trade\n\
     \t ; sym ; print\n\
     \t ; px ; print\n\
     \t ; qty ; print\n\
     \t ; unTrade ; print ... ; print ... ; print\n\
     \t ; Trade(s, p, q) -> q ; print",
     ["AAPL", "191.25", "100", "AAPL", "191.25", "100", "100"], "")
    -- a projection is an ORDINARY WORD: it quotes, it maps, and a
    -- nested pattern reaches a field of a field
  , ("data Pt = (x: Float, y: Float)\n\
     \data Seg = (from: Pt, to: Pt)\n\
     \def s = (0.0 1.0 ; Pt) (2.0 3.0 ; Pt) ; Seg\n\
     \s ; from ; y ; print\n\
     \((s ; from) ((s ; to) nil ; cons) ; cons) ; [x] ... ; map ; printAll\n\
     \s ; Seg(Pt(a, b), q) -> b ; print",
     ["1.0", "0.0", "2.0", "1.0"], "")
    -- ...and it REFLECTS, like every other compiler-written word
  , ("data Trade = (sym: Str, px: Float, qty: Int)\n\
     \[px] ; reflect ; ((c -> c ; unparse ; print) | print) ; merge",
     ["px"], "")
    -- ...and because the rewrite lands on an ordinary binder, `reflect`
    -- is free: the two spellings reflect to the SAME code, character
    -- for character.
  , ("data Dual = Float Float\n\
     \def getCode = reflect ; ((c -> c) | drop ; nil) ; merge\n\
     \([Dual(a, da) -> da a ; Dual] ; getCode ; unparse) \
     \([unDual ; (a da -> da a ; Dual)] ; getCode ; unparse) \
     \; eq? ; verdict ; print",
     ["alt1()"], "")
    -- FUNCTORS (stage 3): `use` grows a third kind of name.  A functor
    -- is any pure `Code ⇒ Code` word; the scope's body is reified, the
    -- word RUNS at elaboration, and the result is spliced back and
    -- re-inferred.  Here `Traced` weaves a trace after every stage.
    -- FLOAT (2026-09-14).  THE DISPLAY CONVENTION, pinned: the shortest
    -- decimal that reads back as the same Double, never in exponent
    -- notation, always with a point.  So every finite Float prints as a
    -- Float LITERAL — `0.1 fadd 0.2` prints the seventeen digits that
    -- are true rather than the three that are convenient.
  , ("0.5 ; print\n2.0 ; print\n-0.0 ; print\n(1.0 3.0 ; fdiv) ; print\n(2.0 ; fsqrt) ; print\n(0.1 0.2 ; fadd) ; print\n(7 ; toFloat) ; print\n(-2.7 ; floor) ; print\n(2.0 ; fexp) ; print",
     ["0.5", "2.0", "-0.0", "0.3333333333333333", "1.4142135623730951",
      "0.30000000000000004", "7.0", "-3", "7.38905609893065"], "")
    -- every Float word once, against hand arithmetic
  , ("(2.0 3.5 ; fadd) ; print\n(2.0 3.5 ; fsub) ; print\n(2.0 3.5 ; fmul) ; print\n(3.0 2.0 ; fdiv) ; print\n(2.5 ; fneg) ; print\n(-2.5 ; fabs) ; print\n(0.0 ; fsin) ; print\n(0.0 ; fcos) ; print\n(1.0 2.0 ; flt? ; verdict) ; print\n(2.0 1.0 ; flt? ; verdict) ; print",
     ["5.5", "-1.5", "7.0", "1.5", "-2.5", "2.5", "0.0", "1.0",
      "alt1()", "alt2()"], "")
    -- `eq?` on Floats is STRUCTURAL — the two doubles, not an epsilon
  , ("((0.1 0.2 ; fadd) 0.3 ; eq? ; verdict) ; print\n(0.3 0.3 ; eq? ; verdict) ; print",
     ["alt2()", "alt1()"], "")
    -- a Float literal travels the reflective pipeline as an ordinary
    -- ATOM: `Atom`'s literal alternatives stay three, so `foldAtom`
    -- keeps its arity and every reflective program keeps its shape,
    -- and the literal round-trips through unparse/parse by its name
  , ("[2.5 ... ; fmul] ; reflect ; ((c -> c ; unparse ; print) | print) ; forget\n[2.5 ... ; fmul] ; reflect ; ((c -> [2.5 ... ; fmul] c 3.0 ; evalAs ; print) | print) ; forget",
     ["2.5 pass >> fmul", "alt1(7.5)"], "")
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef trace   = dup ... >> print ...\ndef weave   = (f h -> [(s -> (s >> pack) h >> append)] f >> flatMap)\ndef tracer  = (f -> f ([trace] >> getCode) >> weave)\nfunctor Traced = tracer\ndef process =\n    use Traced\n    dup >> *\n    2 _ >> *\n7 >> process >> print",
     ["7", "49", "2", "98", "98"], "")
    -- an identity functor changes nothing
  , ("def idF = (c -> c)\nfunctor Same = idF\ndef p = use Same ; 1 ... >> +\n3 >> p >> print",
     ["4"], "")
    -- three kinds of name in ONE header: model renames, resource
    -- routes, functor rewrites — in that order
  , ("resource Log = Str\ndef note = unLog _ >> cat >> Log\ntheory Sink(a) =\n    emit : a ⇒ a\nmodel Loud : Sink(Int) =\n    emit = dup >> *\ndef idF = (c -> c)\nfunctor Same = idF\ndef run =\n    use Log Loud Same\n    emit\n    toStr\n    note\n(\"\" >> Log) 5 >> run >> unLog >> print",
     ["25"], "")
    -- STAGE 4: the checked interposition.  A marker reads no wire —
    -- `ρ =IO> ρ` — so `interpose` admits it at every cut
  , ("def tick = [\"tick\" ... >> print ...] >> getCode\ndef ticked = tick ... >> interpose\nfunctor Ticked = ticked\ndef twice = use Ticked >> dup >> +\n21 >> twice >> print",
     ["tick", "tick", "42"], "")
    -- a resource endomorphism `Fuel ρ ⇒ Fuel ρ` is admitted too, and
    -- meters every stage of the ROUTED program (the claim stage
    -- `use Fuel` writes, then six cuts of arithmetic)
  , ("resource Fuel = Int\ndef burn = unFuel >> _ 1 >> - >> Fuel\ndef metered = ([burn ...] >> getCode) ... >> interpose\nfunctor Metered = metered\ndef poly =\n    use Fuel Metered\n    dup >> *\n    dup >> +\n    _ 1 >> +\n(10 >> Fuel) 5 >> poly >> _ print >> unFuel >> print",
     ["51", "3"], "")
    -- the marker tracer of examples/traced.braid: the stage's text is
    -- the marker's content, so it lifts everywhere a wire-reading
    -- trace could not
  , ("def orNil = ((c -> c) | drop >> nil) >> merge\ndef markStage = (s -> \"\\\"after \" (s >> pack >> unparse) >> cat >> _ \"\\\" ... >> print ...\" >> cat >> parse >> orNil)\ndef marked = [(s -> (s >> pack) (s >> markStage) >> append)] ... >> stagewise\nfunctor Traced = marked\ndef poly = use Traced >> dup >> * >> _ 1 >> +\n5 >> poly >> print",
     ["after dup", "after *", "after _ 1", "after +", "26"], "")
    -- by-generators functors: stagewise and atomwise are flatMaps on
    -- the spine
  , ("[dup >> +] >> getCode >> [(s -> (s >> pack) (s >> pack) >> append)] ... >> stagewise >> unparse >> print",
     ["dup >> dup >> + >> +"], "")
  , ("[dup >> +] >> getCode >> [single] ... >> atomwise >> unparse >> print",
     ["dup >> +"], "")
    -- lift2: a Code ⇒ Code functor lifted to Fn ⇒ Fn at runtime, the
    -- program its own witness — metered where the result types, and
    -- the original where it does not
  , ("resource Fuel = Int\ndef burn = unFuel >> _ 1 >> - >> Fuel\ndef metered = ([burn ...] >> getCode) ... >> interpose\n([metered] [use Fuel >> dup >> *] >> lift2) (10 >> Fuel) 5 >> ev >> _ print >> unFuel >> print",
     ["25", "7"], "")
  , ("resource Fuel = Int\ndef burn = unFuel >> _ 1 >> - >> Fuel\ndef metered = ([burn ...] >> getCode) ... >> interpose\n([metered] [dup >> *] >> lift2) 5 >> ev >> print",
     ["25"], "")
    -- DECIDED laws (§12.9): `sameCode` normalizes both programs in the
    -- free cartesian category over their words and compares.  `same`
    -- means equal under EVERY interpretation — a proof, not a test.
  , ("[dup ; swap] [dup] ; sameCode ; (\"same\" | \"differ\") ; merge ; print",
     ["same"], "")
  , ("[dup ; _ drop] [id] ; sameCode ; (\"same\" | \"differ\") ; merge ; print",
     ["same"], "")
  , ("[dup ; _ dup] [dup ; dup _] ; sameCode ; (\"same\" | \"differ\") ; merge ; print",
     ["same"], "")
    -- naturality of copy, over an ARBITRARY word: the payoff, since no
    -- amount of sampling quantifies over inputs
  , ("[dup ; toStr toStr] [toStr ; dup] ; sameCode ; (\"same\" | \"differ\") ; merge ; print",
     ["same"], "")
  , ("[swap] [id id] ; sameCode ; (\"same\" | \"differ\") ; merge ; print",
     ["differ"], "")
    -- applying a word to one copy is not applying it to both
  , ("[toStr ; dup] [dup ; toStr _] ; sameCode ; (\"same\" | \"differ\") ; merge ; print",
     ["differ"], "")
  , ("[1 ...] [2 ...] ; sameCode ; (\"same\" | \"differ\") ; merge ; print",
     ["differ"], "")
    -- the HONEST limit: `*` and `+` are uninterpreted here, so a law
    -- true of Int arithmetic is not true of every interpretation and is
    -- reported as differing.  `same` is a proof; `differ` is not a
    -- disproof at any particular type.
  , ("[2 _ ; *] [dup ; +] ; sameCode ; (\"same\" | \"differ\") ; merge ; print",
     ["differ"], "")
    -- STAGE 5b PART 2 (2026-09-13): the normalizer enters quotations
    -- and rows.  `sameCode` now runs abstraction elimination first —
    -- the path `reflect` takes — so it decides the binders it used to
    -- refuse, and agrees with `sameCodeC` (§12.9).
  , ("def v = (\"same\" | \"differ\") >> merge\n\
     \[(x -> x x)] [dup] >> sameCode >> v >> print\n\
     \[(a b -> b a)] [swap] >> sameCode >> v >> print\n\
     \[(x -> [x])] [(y -> [y])] >> sameCode >> v >> print",
     ["same", "same", "same"], "")
    -- a QUOTATION is a VALUE the normalizer compares: two quotes are
    -- equal when their captures are equal and their bodies are the same
    -- morphism, decided one level down
  , ("def v = (\"same\" | \"differ\") >> merge\n\
     \[[dup]] [[dup]] >> sameCode >> v >> print\n\
     \[[dup >> swap]] [[dup]] >> sameCode >> v >> print\n\
     \[[+]] [[-]] >> sameCode >> v >> print",
     ["same", "same", "differ"], "")
    -- β for the EXPONENTIAL: `[p] ; ev = p`, and `capture ; ev` is
    -- substitution (the body runs on its captures, then the segment)
  , ("def v = (\"same\" | \"differ\") >> merge\n\
     \[[dup] ... >> ev] [dup] >> sameCode >> v >> print\n\
     \[[dup >> +] ... >> ev] [dup >> +] >> sameCode >> v >> print\n\
     \[[+] ... >> ev] [-] >> sameCode >> v >> print\n\
     \[(x -> x [(y z -> y z >> +)] >> capture >> _ x >> ev)] [(x -> x x >> +)] >> sameCode >> v >> print",
     ["same", "same", "differ", "same"], "")
    -- `ev` OF A WIRE, when the wire's arrow is CLOSED (2026-09-13).  A
    -- hom-object pins it: `Arr(a, b)` unrolls to `Fn⟨a ⇒ b⟩`, one wire
    -- in and one out, so applying it is a neutral application and the
    -- category axioms of every Arrow model built that way decide.
    -- ETA comes with it — `embed [pass] ; f = f` weighs a quotation
    -- against the wire itself — and `capture` of such a wire is the
    -- partial application it denotes.
  , ("data Arr(a, b) = Fn⟨a ⇒ b⟩\n\
     \def v = (\"same\" | \"differ\") >> merge\n\
     \def comp = (f g -> [(x -> f >> unArr >> _ x >> ev >> (y -> g >> unArr >> _ y >> ev))] >> Arr)\n\
     \[(f g h -> f g >> comp >> _ h >> comp)] [(f g h -> f (g h >> comp) >> comp)] >> sameCode >> v >> print\n\
     \[(f -> ([_] >> Arr) f >> comp)] [(f -> f)] >> sameCode >> v >> print\n\
     \[(f -> f ([_] >> Arr) >> comp)] [(f -> f)] >> sameCode >> v >> print\n\
     \[[_ 1 >> + >> _ 2 >> *] >> Arr] [([_ 1 >> +] >> Arr) ([_ 2 >> *] >> Arr) >> comp] >> sameCode >> v >> print\n\
     \[(f x -> f >> unArr >> _ x >> ev)] [(f x -> x (f >> unArr) >> capture >> ev)] >> sameCode >> v >> print\n\
     \[(f g -> f g >> comp)] [(f g -> g f >> comp)] >> sameCode >> v >> print",
     ["same", "same", "same", "same", "same", "differ"], "")
    -- β for the COPRODUCT at an injection the normalizer knows: follow
    -- the tag, run that track, re-tag.  No branching needed.
  , ("def v = (\"same\" | \"differ\") >> merge\n\
     \[dup >> alt1 >> (+ | -) >> merge] [dup >> +] >> sameCode >> v >> print\n\
     \[dup >> alt2 >> (+ | -) >> merge] [dup >> -] >> sameCode >> v >> print\n\
     \[dup >> alt2 >> (+ | -) >> merge] [dup >> +] >> sameCode >> v >> print\n\
     \[toStr >> alt1 >> (alt1 | alt2) >> merge >> merge] [toStr] >> sameCode >> v >> print",
     ["same", "same", "differ", "same"], "")
    -- THE CASE SPLIT: a row over a sum whose injection is UNKNOWN
    -- (`eq? : a a => (a a | a a)`, a closed two-track row).  η, the
    -- track swap, the identity row, and the codiagonal's coherence —
    -- each proved at EVERY input, not sampled.  The residual is
    -- compared semantically: `(f | ---)` and `(f | pass)` are one
    -- morphism here, and a different second track is not.
  , ("def v = (\"same\" | \"differ\") >> merge\n\
     \[eq? >> (alt1 | alt2) >> merge] [eq?] >> sameCode >> v >> print\n\
     \[eq? >> (alt2 | alt1) >> merge] [eq?] >> sameCode >> v >> print\n\
     \[eq? >> (pass | pass)] [eq?] >> sameCode >> v >> print\n\
     \[eq? >> (+ | +) >> merge] [eq? >> merge >> +] >> sameCode >> v >> print\n\
     \[eq? >> (toStr toStr | ---)] [eq? >> (toStr toStr | pass)] >> sameCode >> v >> print\n\
     \[eq? >> (toStr toStr | ---)] [eq? >> (toStr toStr | toStr toStr)] >> sameCode >> v >> print",
     ["same", "differ", "same", "same", "same", "differ"], "")
    -- `into`'s own two equations, which is what pins a copairing:
    -- [h, id] . alt1 = h, and [h, id] . alt(k+1) = alt(k)
  , ("def v = (\"same\" | \"differ\") >> merge\n\
     \[alt1 >> [toStr >> alt1] ... >> into] [toStr >> alt1] >> sameCode >> v >> print\n\
     \[alt2 >> [toStr >> alt1] ... >> into] [alt1] >> sameCode >> v >> print\n\
     \[alt1 >> [toStr >> alt1] ... >> into] [alt1] >> sameCode >> v >> print\n\
     \[alt1 >> [toStr >> alt1] ... >> into >> there >> merge] [toStr] >> sameCode >> v >> print",
     ["same", "same", "differ", "same"], "")
    -- the prelude's coproduct layer, decided: `dist2`/`undist2` are
    -- inverse where they are defined, and `case2`/`case3`/`cond`/
    -- `otherwise` are the bare row they expand to.  `case2` is the one
    -- that matters: eliminating its binders EMITS `dist2`, so this is
    -- the closed structure checking its own derivation.
  , ("data Pair = (Int Int | Int Int)\n\
     \def v = (\"same\" | \"differ\") >> merge\n\
     \def viaCase2 = (s -> [+] [-] s >> case2)\n\
     \def viaRow   = (s -> s >> (+ | -) >> merge)\n\
     \def viaCase3 = (s -> [+] [-] [*] s >> case3)\n\
     \def viaRow3  = (s -> s >> (+ | (- | *) >> merge) >> merge)\n\
     \def viaCond  = (b -> b [1] [2] >> condFn >> ev)\n\
     \def viaRowC  = (b -> b >> (1 | 2) >> merge)\n\
     \def viaOther = (s -> s [drop drop >> 1] >> otherwise)\n\
     \def viaRowO  = (s -> s >> (pass | drop drop >> 1) >> merge)\n\
     \[_ unPair >> dist2 >> merge] [_ unPair >> _ merge] >> sameCode >> v >> print\n\
     \[unPair >> undist2 >> dist2 >> merge] [unPair >> merge] >> sameCode >> v >> print\n\
     \[viaCase2] [viaRow] >> sameCode >> v >> print\n\
     \[viaCase3] [viaRow3] >> sameCode >> v >> print\n\
     \[viaCond] [viaRowC] >> sameCode >> v >> print\n\
     \[viaOther] [viaRowO] >> sameCode >> v >> print",
     ["same", "same", "same", "same", "same", "same"], "")
    -- `sameCode` and `sameCodeC` are ONE procedure now, so they must
    -- agree on every program: a dozen, spanning binders, quotations,
    -- known injections, case splits, a residual, `into`, and the
    -- arithmetic law neither can see
  , ("def v = (\"same\" | \"differ\") >> merge\n\
     \def agree = (a b -> (a b >> sameCode) ((a >> getCode) (b >> getCode) >> sameCodeC) >> eq? >> (drop drop >> \"agree\" | drop drop >> \"DISAGREE\") >> merge >> print)\n\
     \[(x -> x x)] [dup] >> agree\n\
     \[(a b -> b a)] [swap] >> agree\n\
     \[(x -> [x])] [(y -> [y])] >> agree\n\
     \[[dup >> swap]] [[dup]] >> agree\n\
     \[[dup] ... >> ev] [dup] >> agree\n\
     \[dup >> alt1 >> (+ | -) >> merge] [dup >> +] >> agree\n\
     \[dup >> alt2 >> (+ | -) >> merge] [dup >> +] >> agree\n\
     \[eq? >> (alt1 | alt2) >> merge] [eq?] >> agree\n\
     \[eq? >> (alt2 | alt1) >> merge] [eq?] >> agree\n\
     \[eq? >> (drop drop >> 1 | ---)] [eq? >> (drop drop >> 1 | pass)] >> agree\n\
     \[alt1 >> [toStr >> alt1] ... >> into] [toStr >> alt1] >> agree\n\
     \[2 _ >> *] [dup >> +] >> agree",
     ["agree", "agree", "agree", "agree", "agree", "agree",
      "agree", "agree", "agree", "agree", "agree", "agree"], "")
  ] ++
    -- forward reference across the model boundary, at RUNTIME: the
    -- module's own defs are mutually visible, so a slot body calling a
    -- def written after it resolves
  [ ("theory Monoid(a) =\n    unit : • ⇒ a\n    op   : a a ⇒ a\ndef myAdd = +\nmodel S : Monoid(Int) =\n    unit = 0\n    op   = myAdd\ndef total = use S ; [op] unit ... ; foldExp\n1 2 3 >> total >> print",
     ["6"], "")
  ] ++
  [ ("1 2 >> (1 ... >> +) (2 _ >> *) >> + >> print", ["6"],  "")   -- succ, double
  , ("1 2 >> swap",                        [],     "2 1")
  , ("1 2 3 >> (1 ... >> +) ... >> + ...",   [],     "4 3")
  , ("1 2 3 >> (1 ... >> +) >>> + ...",      [],     "4 3")
  , ("def square = dup >> *\n5 >> square >> print", ["25"], "")
  , ("true false",                         [],     "alt1() alt2()")
  , ("1 2\nswap\nprint ...\nprint",        ["2", "1"], "")
  , ("1\n2 id",                            [],     "2 1")
  , ("1\n2 ...",                           [],     "2 1")

    -- the naming binder is identity at runtime: the wires it names go
    -- straight back out, and each later mention of a name is a copy
  , ("1 2 3\n-> a b c\npass",             [],     "1 2 3")   -- pure id
    -- a whole stack through one wire, and back
  , ("data B(...) = (...)\n1 \"a\" >> B >> unB", [], "1 a")
    -- boxed cells give a pair-list the WHOLE library, not just foldList
  , ("[(bx -> bx >> unBox >> (n s -> s >> drop >> n))] (1 \"a\" 2 \"b\" >> pack2) >> map >> [0] [(a n -> a n >> +)] ... >> foldList >> print", ["3"], "")
    -- mapN/mapN2: the bundle tier can rebuild its own container now,
    -- so ANY one- or two-wire word lifts pointwise.  addN and scaleN
    -- are derived from them (they used to be primitives).
  , ("[2 _ >> *] 1 2 3 4 >> mapN >> sumN >> print", ["20"], "")
  , ("1 2 3 10 20 30 >> addN >> sumN >> print",   ["66"],  "")
  , ("1 2 3 10 20 30 >> mulN >> sumN >> print",   ["140"], "")
  , ("1 2 3 10 20 30 >> subN >> sumN >> print",   ["-54"], "")
  , ("3 1 2 3 >> scaleN >> sumN >> print",        ["18"],  "")
    -- lift a word the prelude does not ship, in one line
  , ("def maxN = zipN >> [(x y -> (x y >> less) [y] [x] ... >> cond)] ... >> mapN2\n1 9 3 5 2 7 >> maxN >> sumN >> print", ["21"], "")
    -- unzipN is zipN's inverse
  , ("1 2 3 10 20 30 >> zipN >> unzipN >> addN >> sumN >> print", ["66"], "")
  , ("[dup >> *] 1 2 3 >> mapN >> sumN >> print",   ["14"], "")
  , ("[dup >> *] >> mapN >> sumN >> print",         ["0"],  "")
    -- INDICES at runtime.  A Fin is a bare Int: the bound is a type,
    -- erased like every other width, so weaken/finInt are identities.
    -- grades are erased: several effectful atoms run left-to-right,
    -- deepest wire first — the order they are written in
  , ("1 2 3 >> print print print",        ["1","2","3"], "")
    -- laws RUN at module start; a passing model is transparent
  , ("theory M(a) =\n    unit : • ⇒ a\n    op : a a ⇒ a\n    sample : • ⇒ a\n    law leftUnit = (sample ; unit ... ; op) sample ; eq? ; (forget ; true | forget ; false) ; merge\nmodel Good : M(Int) =\n    unit = 0\n    op = +\n    sample = 7\ndef t = use Good ; [op] unit ... ; foldExp\n1 2 3 >> t >> print", ["6"], "")
    -- STAGE 5a: a LAW that uses a slot-local variable.  `box : b ⇒ a`
    -- is polymorphic in b, so the law may call it at Int while the
    -- theory's own parameter is Str — which is the point of the
    -- variable being local to the slot rather than to the theory.
  , ("theory Wrap(a) =\n    box : b ⇒ a\n    sample : • ⇒ a\n    law boxOne = (1 ; box) sample ; eq? ; (forget ; true | forget ; false) ; merge\nmodel W : Wrap(Str) =\n    box = toStr\n    sample = \"1\"\ndef w = use W ; box\n5 >> w >> print",
     ["5"], "")
    -- STAGE 5a: a theory over a type CONSTRUCTOR, composed and run
  , ("data K(a, b) = Fn⟨a ⇒ b⟩\ntheory Arrow(k(_, _)) over Doctrine =\n    embed   : Fn⟨a ⇒ b⟩ ⇒ k(a, b)\n    compose : k(a, b) k(b, c) ⇒ k(a, c)\nmodel P : Arrow(K) =\n    embed  = K\n    compose = (f g -> [(x -> f ; unK ; _ x ; ev ; (y -> g ; unK ; _ y ; ev))] ; K)\ndef run2 = over P ; [_ 1 ; +] ... ; embed ... ; _ [_ 2 ; *] ; _ embed ; compose ; unK ; _ 5 ; ev\nrun2 >> print",
     ["12"], "")
  , ("10 20 30 >> indicesN",              [],  "0 10 1 20 2 30")
  , ("fin0 10 20 30 >> at >> print",      ["10"], "")   -- 0 = DEEPEST
  , ("fin1 10 20 30 >> at >> print",      ["20"], "")
  , ("fin2 >> finInt >> print",           ["2"],  "")
  , ("fin1 >> weaken >> _ 10 20 30 40 >> at >> print", ["20"], "")
    -- the DYNAMIC witness: checked against the live segment's width
  , ("1 10 20 30 >> checkedAt >> (at >> print | forget >> \"oob\" >> print) >> merge", ["20"], "")
  , ("7 10 20 30 >> checkedAt >> (at >> print | forget >> \"oob\" >> print) >> merge", ["oob"], "")
  , ("0 0 >> checkedAt >> (at >> print | forget >> \"oob\" >> print) >> merge", ["0"], "")
    -- an index literal is a closed point, so it reflects like any
    -- other literal (not an open-arity word)
  , ("[fin1 10 20 30 >> at] >> reflect >> ((c -> [10] c >> evalAs >> print) | print) >> forget", ["alt1(20)"], "")
    -- STAGE 5a½: an `evalAs` WITNESS is a written type, so an
    -- unlabelled one refuses recursive code — the sandbox reads `Recursive`
    -- exactly as it reads io, and the refusal rides the miss track
  , ("\"[_ 100 >> less?] [2 _ >> *] ... >> while\" >> parse >> ((c -> [dup >> *] c (7) >> evalAs >> print) | print) >> forget",
     ["alt2(Cannot unify effects: Recursive vs pure (the expected type fixes the grade; this code must stay pure), 7)"], "")
    -- a witness that itself recurses is `=Recursive>`, and then the same
    -- code is admitted
  , ("\"[_ 100 >> less?] [2 _ >> *] ... >> while\" >> parse >> ((c -> [[_ 200 >> less?] [3 _ >> *] ... >> while] c (7) >> evalAs >> print) | print) >> forget",
     ["alt1(112)"], "")
    -- STAGE 5e: a MARKED def reflects and runs like any other — the
    -- elaborated body is a closed spine, so `reflect` is total on it
    -- and the label rides through the witness
  , ("def decr = _ 1 >> -\n\
     \def fac = use Recursive ; (n -> n >> zero? >> ((z -> 1) | (m -> m (m >> decr >> fac) >> *)) >> merge)\n\
     \[fac] ([fac] >> getCode) (5) >> evalAs >> (print | print forget) >> merge",
     ["120"], "")
  , ("def decr = _ 1 >> -\n\
     \def fac = use Recursive ; (n -> n >> zero? >> ((z -> 1) | (m -> m (m >> decr >> fac) >> *)) >> merge)\n\
     \[dup >> *] ([fac] >> getCode) (5) >> evalAs >> (print | print forget) >> merge",
     ["Cannot unify effects: Recursive vs pure (the expected type fixes the grade; this code must stay pure)"], "")
    -- a FUNCTOR on the same header sees the closed spine: `use Ticked
    -- Recursive` traces every stage of the knot, on every re-entry
  , ("def tick = [\"tick\" ... >> print ...] >> getCode\n\
     \def ticked = tick ... >> interpose\n\
     \functor Ticked = ticked\n\
     \def down = use Ticked Recursive ; (n -> n >> zero? >> ((z -> 0) | (m -> m >> _ 1 >> - >> down)) >> merge)\n\
     \2 >> down >> print",
     ["tick", "tick", "tick", "0"], "")
    -- OPEN recursion still works: `fix` takes a body someone else
    -- wrote, and a wrapper around that body is a different knot
  , ("def decr = _ 1 >> -\n\
     \def facBody = [(self n -> n >> zero? >> ((z -> 1) | (m -> m (m >> decr >> self ... >> ev) >> *)) >> merge)]\n\
     \def loud = (b -> [(self ... -> (\"step\" >> print) ... >> self ... >> b ... >> ev)])\n\
     \def facLoud = facBody ... >> loud ... >> fix ... >> ev\n\
     \3 >> facLoud >> print",
     ["step", "step", "step", "step", "6"], "")
    -- STAGE 5a⁹⁄₁₀ — THE RULE THE PRIM REDUCTION WAS MISSING.  Every
    -- derived higher-order prelude word is checked to be AT LEAST AS
    -- GENERAL as the scheme its prim ancestor had, by the one routine
    -- that states that question (`subsumes`, reached here through
    -- `checkInstance`): a theory whose slots ARE the old schemes, and
    -- a model filling each with today's word.  Written at wire
    -- granularity because a theory slot has one slot-local stack; the
    -- grades, which is what this stage moved, are exact.
    -- Under unifying grades `loopD`, `whileD` and `untilD` all failed
    -- here ("Recursive vs pure ... written and fixed").
    -- `fixD` joined the theory when `fix` left the prim set (5e).  Its
    -- slot is written `=Recursive>` where the PRIM's own arrow was
    -- pure: the derived word runs the knot's `ev`, and the scope it is
    -- written under mints unconditionally.  Everything INSIDE the
    -- arrow — the body's grade, the knot's — is unchanged.
  , ("theory Derived =\n    fixD       : Fn⟨Fn⟨a =Recursive> b⟩ a ⇒ b⟩ =Recursive> Fn⟨a =Recursive> b⟩\n    loopD      : Fn⟨a ⇒ (a | b)⟩ a =Recursive> b\n    whileD     : Fn⟨a ⇒ (b | c)⟩ Fn⟨b ⇒ a⟩ a =Recursive> c\n    untilD     : Fn⟨a ⇒ (b | c)⟩ Fn⟨c ⇒ a⟩ a =Recursive> b\n    case2D     : Fn⟨a ⇒ b⟩ Fn⟨c ⇒ b⟩ (a | c) ⇒ b\n    curryD     : Fn⟨a b ⇒ c⟩ ⇒ Fn⟨a ⇒ Fn⟨b ⇒ c⟩⟩\n    captureD   : a Fn⟨a b ⇒ c⟩ ⇒ Fn⟨b ⇒ c⟩\n    liftD      : Fn⟨a ⇒ b⟩ ⇒ Fn⟨c a ⇒ c b⟩\n    boxD       : Fn⟨a ⇒ b⟩ Code ⇒ Fn⟨a ⇒ (b | Str a)⟩\n    lift2D     : Fn⟨Code ⇒ Code⟩ Fn⟨a ⇒ b⟩ ⇒ Fn⟨a ⇒ b⟩\n    mapD       : Fn⟨a ⇒ b⟩ List(a) ⇒ List(b)\n    foldD      : Fn⟨a b ⇒ a⟩ a List(b) ⇒ a\n    filterD    : Fn⟨a ⇒ (b | c)⟩ List(a) ⇒ List(b)\n    flatMapD   : Fn⟨a ⇒ List(b)⟩ List(a) ⇒ List(b)\n    condD      : Bool Fn⟨a ⇒ b⟩ Fn⟨a ⇒ b⟩ a ⇒ b\n    stagewiseD : Fn⟨a ⇒ List(b)⟩ List(a) ⇒ List(b)\n    getCodeD   : Fn⟨a ⇒ b⟩ ⇒ Code\n    negateD    : Fn⟨a ⇒ (b | c)⟩ ⇒ Fn⟨a ⇒ (c | b)⟩\n    otherwiseD : (a | b) Fn⟨b ⇒ a⟩ ⇒ a\n    ifRouteD   : a Fn⟨a ⇒ (b | c)⟩ Fn⟨b ⇒ d⟩ ⇒ (d | c)\n\nmodel D : Derived =\n    fixD       = fix\n    loopD      = loop\n    whileD     = while\n    untilD     = until\n    case2D     = case2\n    curryD     = curry\n    captureD   = capture\n    liftD      = lift\n    boxD       = box\n    lift2D     = lift2\n    mapD       = map\n    foldD      = fold\n    filterD    = filter\n    flatMapD   = flatMap\n    condD      = cond\n    stagewiseD = stagewise\n    getCodeD   = getCode\n    negateD    = negate\n    otherwiseD = otherwise\n    ifRouteD   = ifRoute\n\n\"ok\" >> print", ["ok"], "")
    -- …and the consequence, run: a WRITTEN pure `Fn⟨Int ⇒ (Int|Int)⟩`
    -- in a data field reaches `loop`, which no derived word could take
    -- while composition unified grades.
  , ("data Step = Fn⟨Int ⇒ (Int | Int)⟩\ndef lt100? = _ 100 >> lt? >> (_ drop | _ drop)\ndef double = 2 _ >> *\ndef boxed = [lt100? >> (double >> again | done) >> merge] ... >> Step\nboxed >> unStep >> _ 7 >> loop >> print",
     ["112"], "")
    -- the sandbox reads the order the other way too: a written pure
    -- VALUE flows into an `=IO>` expectation (∅ is the bottom)
  , ("\"dup >> *\" >> parse >> ((c -> [dup >> * >> dup >> print ...] c (7) >> evalAs >> print) | print) >> forget",
     ["alt1(49)"], "")
  , ("1 >> sumN _",                                 [],     "0 1")
  , ("5\n-> x\nx ... >> + >> print",       ["10"], "")
  , ("10 20 30\n-> h m f\nsumN >> print\nh m f >> sumN >> print",
                                           ["60", "60"], "")
  , ("7\n-> x\ndrop\nx x >> *",            [],     "49")   -- name outlives wire

    -- quotations and ev
  , ("[dup >> *] 7 >> ev >> print",     ["49"], "")   -- from the spec
  , ("[1 2 >> +] >> ev >> print",       ["3"],  "")
  , ("[pass]",                             [],     "[fn]")
  , ("def sq = [dup >> *]\nsq 5 >> ev", [],     "25")
    -- tails-only closing: a non-final def keeps its element-internal
    -- polymorphism (q's quoted pass applies to whatever follows)
  , ("def q = [pass]\nq 1 >> ev",        [],     "1")

  , ("5 >> negative?",                     [],     "alt2(5)")

    -- grouping
  , ("7 >> (dup >> *) >> print",           ["49"], "")
  , ("5 8 >> (1 ... >> +) (1 ... >> +) >> + >> print", ["15"], "")

    -- named abstractions
  , ("7 >> (x -> x x >> *) >> print",      ["49"], "")
  , ("7 >> (x -> x 1 >> +) >> print",      ["8"],  "")   -- spec: produces 8
  , ("3 4 >> (x y -> y x >> +) >> print",  ["7"],  "")
  , ("1 2 >> (x y -> x) >> print",         ["1"],  "")   -- unused y deleted
  , ("def sq = (x -> x x >> *)\n5 >> sq >> print", ["25"], "")
    -- closure: the quotation captures x at reification
  , ("7 >> (x -> [x 1 >> +]) >> ev >> print",   ["8"], "")

    -- sums: injections, code rows, merge
  , ("5 >> alt1 >> (dup >> * | ---) >> merge >> print",       ["25"], "")
    -- `into` (5a⅞): the OPEN eliminator.  Peel one alternative and
    -- tag-shift the rest — three tracks, three answers, then the
    -- existing `otherwise` closes what is left.
  , ("data T3 = (Int | Str | Sym)\ndef peel = unT3 >> [toStr >> alt1] ... >> into >> _ [drop >> \"sym\"] >> otherwise\n7 >> alt1 >> T3 >> peel >> print\n\"hi\" >> alt2 >> T3 >> peel >> print\n.tok >> alt3 >> T3 >> peel >> print",
     ["7", "hi", "sym"], "")
    -- two tracks: the handler runs on tag 0, and on tag 1 the tag shifts
    -- down into a 1-ary sum, which `there >> merge` un-sums
  , ("5 >> alt1 >> [toStr >> alt1] ... >> into >> there >> merge >> print\n\"x\" >> alt2 >> [toStr >> alt1] ... >> into >> there >> merge >> print",
     ["5", "x"], "")
    -- THE ELGOT IDENTITY, `loop f = f >> [loop f] into` up to un-summing.
    -- 5a½ listed the iteration axiom as "statable, not yet run"; with
    -- `into` it is a program, checked at sample points.  RUNNABLE, NOT
    -- DECIDED: `sameCode` does not enter rows yet (5b).
  , ("def step = [(n -> n 10 >> gt? >> (_ drop >> toStr >> alt2 | _ drop >> 2 ... >> * >> alt1) >> merge)]\ndef lhs = (n -> step n >> loop)\ndef rhs = (n -> n >> step ... >> ev >> [(m -> step m >> loop >> alt1)] ... >> into >> there >> merge)\n1 >> lhs >> print\n1 >> rhs >> print\n20 >> lhs >> print\n20 >> rhs >> print\n7 >> lhs >> print\n7 >> rhs >> print",
     ["16", "16", "20", "20", "14", "14"], "")
    -- a written `Fn⟨(A | ---) ⇒ (B | ---)⟩` is an `evalAs` WITNESS: the
    -- residual is part of the expectation the loaded code must meet.
    -- (The pipeline stays pure — a written pure witness refuses io.)
  , ("data Peeler(---) = Fn⟨(Int | ---) ⇒ (Str | ---)⟩\ndef getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef w = [(s -> s >> (toStr | ---))] >> Peeler >> unPeeler\ndef c = (w) >> getCode\n(5 >> alt1) >> (w) (c) ... >> evalAs",
     [], "alt1(alt1(5))")
  , ("7 >> alt2 >> (dup >> * | 1 ... >> +) >> merge >> print", ["8"], "")
  , ("5 >> alt2 >> (drop | ---)",           [],     "alt2(5)")
  , ("1 2 >> alt1",                         [],     "alt1(1, 2)")
  , ("3 4 >> here >> there",               [],     "alt2(3, 4)")
    -- decide-then-inject: predicate is already the fork (Bool ≡ (• | •))
  , ("def classify = even? >> (here | here >> there) >> merge\n4 >> classify",
                                           [],     "alt1(4)")
  , ("def classify = even? >> (here | here >> there) >> merge\n5 >> classify",
                                           [],     "alt2(5)")
    -- routers in flight: quoted routers dispatch via plain ev
  , ("5 >> [odd?] ... >> ev",           [],     "alt1(5)")
  , ("4 >> [odd?] ... >> ev",           [],     "alt2(4)")
    -- if-then-else is route >> row >> merge
  , ("5 >> odd? >> (id | drop >> 0) >> merge >> print", ["5"], "")
  , ("4 >> odd? >> (id | drop >> 0) >> merge >> print", ["0"], "")
    -- loop: Elgot iteration (sum 1..5)
  , ("def decr = (x -> x 1 >> -)\ndef sumStep = (a n -> n >> zero? >> ((z -> a >> done) | (m -> (a m >> +) (m >> decr) >> again)) >> merge)\n0 5 >> [sumStep] ... >> loop >> print", ["15"], "")
    -- the guard machine as a loop body
  , ("0 3 >> [(a n -> n >> zero? >> ((z -> a >> done) | (m -> (a m >> +) (m 1 >> -) >> again)) >> merge)] ... >> loop >> print", ["6"], "")
  , ("5 3 >> - >> print",                  ["2"],  "")
  , ("7 >> (2 _ >> *) >> print",           ["14"], "")
    -- multi-line def bodies + `fix`: the knot is a word, and an OPEN
    -- binder (`self ... ->`) keeps the body point-free
  , ("def lt100? = _ 100 >> lt? >> (_ drop | _ drop)\ndef double = 2 _ >> *\ndef until100 =\n  [ self ... ->\n    lt100?\n    double >> self ... >> ev | _\n    merge ] ...\n  fix ...\n  ev\n7 >> until100 >> print", ["112"], "")
  , ("def decr = _ 1 >> -\ndef lt2? = _ 2 >> lt? >> (_ drop | _ drop)\ndef fib =\n  [ self ... ->\n    lt2?\n    _ | (n -> n >> decr >> self ... >> ev >> _ (n 2 >> - >> self ... >> ev) >> +)\n    merge ] ...\n  fix ...\n  ev\n10 >> fib >> print", ["55"], "")
    -- while, DERIVED in-language: whileFn assembles the loop body
    -- from closures; while = whileFn ... >> loop fuses in the knot
  , ("def lt100? = _ 100 >> lt? >> (_ drop | _ drop)\ndef double = 2 _ >> *\ndef whileFn = (p f -> [p ... >> ev >> (f ... >> ev >> again | done) >> merge])\ndef while = whileFn ... >> loop\n7 >> [lt100?] [double] ... >> while >> print", ["112"], "")
  , ("def lt100? = _ 100 >> lt? >> (_ drop | _ drop)\ndef double = 2 _ >> *\ndef whileFn = (p f -> [p ... >> ev >> (f ... >> ev >> again | done) >> merge])\ndef while = whileFn ... >> loop\n7 >> [lt100?] [double >> double] ... >> while >> print", ["112"], "")
    -- comments: # to end of line, ## docs are inert at runtime
  , ("# header comment\n5 >> print # trailing", ["5"], "")
  , ("## doc for sq2\ndef sq2 = dup >> *\n3 >> sq2 >> print", ["9"], "")
  , ("type MInt = (• | Int)\n5 >> print",        ["5"], "")
    -- data at runtime: bundle, spill, use
  , ("data Person = (Str Int)\n\"ada\" 36 >> Person >> unPerson >> _ drop >> print", ["ada"], "")
  , ("data Person = (Str Int)\n\"ada\" 36 >> Person >> unPerson >> drop ... >> print", ["36"], "")
    -- Peano round-trip: folds by ordinary recursion through unNat
  , ("type Nat = (• | Nat)\ndef fromInt = [(self ... -> zero? >> (drop >> alt1 >> Nat | _ 1 >> - >> self ... >> ev >> alt2 >> Nat) >> merge)] ... >> fix ... >> ev\ndef toInt = [(self ... -> unNat >> (0 | self ... >> ev >> 1 ... >> +) >> merge)] ... >> fix ... >> ev\n3 >> fromInt >> toInt >> print", ["3"], "")
    -- trees: build with rolled injections, fold with recursion
  , ("type Tree(a) = (a | Tree(a) Tree(a))\ndef leaf = alt1 >> Tree\ndef node = alt2 >> Tree\ndef total = [(self ... -> unTree >> (_ | _ (self ... >> ev) >> swap >> _ (self ... >> ev) >> +) >> merge)] ... >> fix ... >> ev\n1 >> leaf >> _ (2 >> leaf) >> node >> _ (4 >> leaf) >> node >> total >> print", ["7"], "")
    -- same folds, by points: [case1] [case2] ... >> foldName
  , ("type Nat = (• | Nat)\ndef fromInt = [(self ... -> zero? >> (drop >> alt1 >> Nat | _ 1 >> - >> self ... >> ev >> alt2 >> Nat) >> merge)] ... >> fix ... >> ev\n3 >> fromInt >> [0] [1 ... >> +] ... >> foldNat >> print", ["3"], "")
  , ("type Tree(a) = (a | Tree(a) Tree(a))\ndef leaf = alt1 >> Tree\ndef node = alt2 >> Tree\n1 >> leaf >> _ (2 >> leaf) >> node >> _ (4 >> leaf) >> node >> [_] [+] ... >> foldTree >> print", ["7"], "")
  , ("type Tree(a) = (a | Tree(a) Tree(a))\ndef leaf = alt1 >> Tree\ndef node = alt2 >> Tree\n1 >> leaf >> _ (2 >> leaf) >> node >> _ (4 >> leaf) >> node >> [drop >> 1] [+] ... >> foldTree >> print", ["3"], "")
    -- prelude defs available with no local definition
  , ("5 >> _ 5 >> equals? >> print",             ["alt1(5)"], "")
  , ("def double = 2 _ >> *\n7 >> [_ 100 >> less?] [double] ... >> while >> print", ["112"], "")
  , ("7 >> [_ 100 >> less? >> not] [dup >> +] ... >> until >> print", ["112"], "")
    -- user defs shadow prelude defs
  , ("def while = drop\n1 2 >> while ... >> print", ["2"], "")
    -- >=>: short-circuiting Kleisli chains; alt1 lifts pure stages
  , ("4 >> (even? >=> zero?) >> print",         ["alt2(4)"], "")
  , ("0 >> (even? >=> zero?) >> print",         ["alt1(0)"], "")
  , ("7 >> (even? >=> zero?) >> print",         ["alt2(7)"], "")
  , ("def double = 2 _ >> *\n4 >> (even? >=> _ 100 >> less? >=> double >> alt1) >> print", ["alt1(8)"], "")
  , ("def double = 2 _ >> *\n120 >> (even? >=> _ 100 >> less? >=> double >> alt1) >> print", ["alt2(120)"], "")
  , ("def double = 2 _ >> *\n7 >> (even? >=> _ 100 >> less? >=> double >> alt1) >> print", ["alt2(7)"], "")
  , ("5 >> (_ 5 >> equals? >=> odd?) >> print",  ["alt1(5)"], "")
    -- ok/miss aliases: return and stay-missed of the sum monad
  , ("def double2 = 2 _ >> *\ndef process = even? >=> _ 100 >> less? >=> double2 >> ok\n4 >> process >> print", ["alt1(8)"], "")
  , ("7 >> odd? >> (ok | zero?) >> merge >> print", ["alt1(7)"], "")
    -- forget (terminal morphism) and verdict: routers to pure decisions
  , ("1 2 3 >> forget", [], "")
  , ("5 >> odd? >> verdict >> print", ["alt1()"], "")
  , ("4 >> odd? >> verdict >> print", ["alt2()"], "")
  , ("3 4 >> eq? >> verdict >> print", ["alt2()"], "")
  , ("4 4 >> eq? >> verdict >> print", ["alt1()"], "")
  , ("3 3 >> equals >> print",  ["alt1()"], "")
  , ("5 3 >> less >> print",    ["alt2()"], "")
  , ("3 5 >> less >> print",    ["alt1()"], "")
  , ("7 >> odd >> print",       ["alt1()"], "")
    -- a Bool drives a choice through an ordinary row
  , ("7 >> odd >> (1 | 0) >> merge >> print", ["1"], "")
  , ("8 >> odd >> (1 | 0) >> merge >> print", ["0"], "")
    -- cond/when/unless: a Bool selects a quotation, run on the segment
    -- (possible ONLY at the verdict tier: Bool's tracks are empty, so
    -- selection commutes past the data)
  , ("3 4 >> (1 >> odd) [+] [*] ... >> cond >> print", ["7"], "")
  , ("3 4 >> (2 >> odd) [+] [*] ... >> cond >> print", ["12"], "")
  , ("5 >> (1 >> odd) [dup >> *] ... >> when >> print", ["25"], "")
  , ("5 >> (2 >> odd) [dup >> *] ... >> when >> print", ["5"], "")
  , ("5 >> (2 >> odd) [dup >> *] ... >> unless >> print", ["25"], "")
    -- strings, symbols, parse routers
  , ("\"hello\" >> print", ["hello"], "")
  , ("\"a\" \"b\" >> cat >> print", ["ab"], "")
  , ("\"Q: \" \"why?\" >> cat >> print", ["Q: why?"], "")
  , ("7 >> toStr >> \"n=\" ... >> cat >> print", ["n=7"], "")
  , (".red .red >> eq? >> verdict >> print", ["alt1()"], "")
  , (".red .blue >> eq? >> verdict >> print", ["alt2()"], "")
  , ("\"42\" >> asInt? >> print", ["alt1(42)"], "")
  , ("\"4x\" >> asInt? >> print", ["alt2(4x)"], "")
    -- REAL column sniffing now: strings in, typed column or evidence out
  , ("(\"1\" \"2\" \"3\" >> pack) >> [asInt?] ... >> map >> sequence >> print", ["alt1(list(1, 2, 3))"], "")
  , ("(\"1\" \"x\" \"3\" >> pack) >> [asInt?] ... >> map >> sequence >> print", ["alt2(x)"], "")
    -- sequence: the List/Sum distributive law — column sniffing is
    -- map parse-router >> sequence
  , ("(1 3 5 >> pack) >> [odd?] ... >> map >> sequence >> print", ["alt1(list(1, 3, 5))"], "")
  , ("(1 4 5 >> pack) >> [odd?] ... >> map >> sequence >> print", ["alt2(4)"], "")
    -- >?> / >!> : guard chains along the miss track (dual of >=>)
    -- asymmetric guard predicates: hit carries nothing (drop-free
    -- actions); the hit carries n, so this IS a Maybe now
  , ("def by3? = (n -> n 3 >> mod >> zero >> (... | n))\ndef fz = by3? >> (\"fizz\" | ---) >!> toStr\n9 >> fz >> print", ["fizz"], "")
  , ("def by3? = (n -> n 3 >> mod >> zero >> (... | n))\ndef fz = by3? >> (\"fizz\" | ---) >!> toStr\n7 >> fz >> print", ["7"], "")
  , ("def by3? = (n -> n 3 >> mod >> zero >> (n | n))\ndef fz = by3? >> (drop >> \"fizz\" | ---) >!> toStr\n9 >> fz >> print", ["fizz"], "")
  , ("def by3? = (n -> n 3 >> mod >> zero >> (n | n))\ndef fz = by3? >> (drop >> \"fizz\" | ---) >!> toStr\n7 >> fz >> print", ["7"], "")
  , ("def by3? = (n -> n 3 >> mod >> zero >> (n | n))\ndef by5? = (n -> n 5 >> mod >> zero >> (n | n))\ndef fz = by3? >> (drop >> \"f\" | ---) >?> by5? >> (drop >> \"b\" | ---) >!> toStr\n10 >> fz >> print", ["b"], "")
  , ("def by3? = (n -> n 3 >> mod >> zero >> (n | n))\ndef by5? = (n -> n 5 >> mod >> zero >> (n | n))\ndef fz = by3? >> (drop >> \"f\" | ---) >?> by5? >> (drop >> \"b\" | ---) >!> toStr\n7 >> fz >> print", ["7"], "")
    -- leading | in a row defaults the first arm to pass (id):
    -- (| f) == (pass | f)
  , ("def k = odd? >> (| dup >> *) >> merge\n5 >> k >> print", ["5"], "")
  , ("def k = odd? >> (| dup >> *) >> merge\n4 >> k >> print", ["16"], "")
  , ("5 >> zero? >> (| drop >> 99) >> merge >> print", ["99"], "")
  , ("0 >> zero? >> (| drop >> 99) >> merge >> print", ["0"], "")
    -- trailing | defaults the LAST arm to pass: (f |) == (f | pass)
  , ("def k = odd? >> (dup >> * |) >> merge\n5 >> k >> print", ["25"], "")
  , ("def k = odd? >> (dup >> * |) >> merge\n4 >> k >> print", ["4"], "")
    -- a comment on the `def =` line still triggers block-body form
  , ("def relu =  # cap below at 0\n negative?\n (drop >> 0 |)\n merge\n-3 >> relu >> print", ["0"], "")
    -- deferred branches: handle one track, pass the rest, handle later
  , ("def c = negative? >> (drop >> \"neg\" |) >> (| zero? >> (drop >> \"zero\" | toStr) >> merge) >> merge\n-3 >> c >> print\n0 >> c >> print\n5 >> c >> print", ["neg", "zero", "5"], "")
    -- no >>, aligned-pipe track columns
  , ("def label =\n odd?\n drop | pass\n \"odd\" | pass\n pass | drop\n pass | \"even\"\n merge\n5 >> label >> print\n4 >> label >> print", ["odd", "even"], "")
    -- factorial / fibonacci / exponentiation, recursive and iterative
  , ("def fac = [(self n -> n >> zero? >> ((z -> 1) | (m -> m (m 1 >> - >> self ... >> ev) >> *)) >> merge)] ... >> fix ... >> ev\n5 >> fac >> print", ["120"], "")
    -- fix over a TWO-WIRE function: Σ and Θ are stacks, not wires, so
    -- the knotted function may take and return any width
  , ("def sums = [(self n -> n >> zero? >> ((z -> 0 0) | (m -> (m 1 >> -) >> self ... >> ev >> (a b -> (a m >> +) (b 1 >> +)))) >> merge)] ... >> fix ... >> ev\n4 >> sums >> pack >> print", ["list(10, 4)"], "")
    -- a fix-using program REIFIES: `fix` is an ordinary atom with an
    -- ordinary scheme, so reflect returns real Code where a `.recurse`
    -- atom used to have no type at all
  , ("[[(self n -> n 1 >> - >> self ... >> ev)] ... >> fix ... >> ev] >> reflect >> ((c -> c >> unparse >> print) | print) >> forget",
     ["[_ dup pass >> _ _ _ 1 >> _ _ - >> dup pass >> _ swap pass >> _ _ ev >> drop drop pass] pass >> fix pass >> ev"], "")
    -- LIMIT LIFTED (stage 5a¾).  The knot arrives as a binder
    -- PARAMETER and the self-call sits inside a row, so this was a
    -- closure and `reflect` refused it ("Unknown primitive: self").
    -- Abstraction elimination now distributes the parameter block over
    -- the row with `dist2` and the body reifies.
  , ("[(self n -> n >> zero? >> ((z -> 1) | (m -> m (m 1 >> - >> self ... >> ev) >> *)) >> merge)] >> reflect >> ((c -> \"reflected\" >> print) | print) >> merge",
     ["reflected"], "")
    -- and the reflected code is ordinary Code: it re-splices and runs
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\n[[(self n -> n >> zero? >> ((z -> 1) | (m -> m (m 1 >> - >> self ... >> ev) >> *)) >> merge)] ... >> fix ... >> ev] ([[(self n -> n >> zero? >> ((z -> 1) | (m -> m (m 1 >> - >> self ... >> ev) >> *)) >> merge)] ... >> fix ... >> ev] >> getCode) (5) >> evalAs >> (print | forget >> \"miss\" >> print) >> merge",
     ["120"], "")
  , ("def fib = [(self n -> n 2 >> lt? >> ((x y -> x) | (x y -> (x 1 >> - >> self ... >> ev) >> _ (x 2 >> - >> self ... >> ev) >> +)) >> merge)] ... >> fix ... >> ev\n10 >> fib >> print", ["55"], "")
  , ("def pow = [(self b e -> e >> zero? >> ((z -> 1) | (m -> b (b (m 1 >> -) >> self ... >> ev) >> *)) >> merge)] ... >> fix ... >> ev\n2 8 >> pow >> print", ["256"], "")
  , ("def fibL = n -> 0 1 n >> [(a b k -> k >> zero? >> ((z -> a >> done) | (m -> b (a b >> +) (m 1 >> -) >> again)) >> merge)] ... >> loop\n20 >> fibL >> print", ["6765"], "")
    -- postfix binder: `x y ->` names the top wires, rest of scope is the
    -- body (same OpenAbs as (x y -> …), now usable bare / as a stage)
  , ("def sq = x -> x x >> *\n5 >> sq >> print", ["25"], "")
  , ("def dst = x1 y1 x2 y2 -> (x2 x1 >> - >> dup >> *) (y2 y1 >> - >> dup >> *) >> +\n0 0 3 4 >> dst >> print", ["25"], "")
    -- mid-pipeline: compute then bind
  , ("def ts =\n dup >> +\n d ->\n d d >> +\n7 >> ts >> print", ["28"], "")
    -- the parenthesized form still works (one code path)
  , ("3 4 >> (x y -> y x >> -) >> print", ["1"], "")
    -- clause products + choose guard fold (|| is GONE; pack2R ladders
    -- give text-order vertical lists)
  , ("([1] [2] [3] >> pack) >> len >> print", ["3"], "")
  , ("([1] [2] [3] >> pack) >> [pass] ... >> map >> len >> print", ["3"], "")
  , ("def sign =\n    [odd?] [dup >> *]\n    [negative?] [drop >> 0] ...\n    pack2R\n7 sign >> choose >> (id | 1 ... >> +) >> merge >> print", ["49"], "")
  , ("def sign = ([odd?] [dup >> *] [negative?] [drop >> 0] >> pack2)\n8 sign >> choose >> (id | 1 ... >> +) >> merge >> print", ["9"], "")
  , ("def sign =\n    [odd?] [dup >> *]\n    [negative?] [drop >> 0] ...\n    pack2R\n-4 sign >> choose >> (id | 1 ... >> +) >> merge >> print", ["0"], "")
    -- no else lane: none hit -> alt2(input)
  , ("5 ([odd?] [dup >> *] >> pack2) >> choose >> (drop >> \"hit\" | drop >> \"miss\") >> merge >> print", ["hit"], "")
  , ("6 ([odd?] [dup >> *] >> pack2) >> choose >> (drop >> \"hit\" | drop >> \"miss\") >> merge >> print", ["miss"], "")
    -- a bound clause value reused; and | sum rows still work
  , ("def og = ([odd?] [drop >> \"odd\"] >> pack2)\n3 og >> choose >> (id | drop >> \"even\") >> merge >> print\n4 og >> choose >> (id | drop >> \"even\") >> merge >> print", ["odd", "even"], "")
  , ("5 >> odd? >> (drop >> \"o\" | drop >> \"e\") >> merge >> print", ["o"], "")
    -- branchless tier: swapIf (Fredkin) and select (mux) route
    -- already-computed values; no quotation runs
  , ("true 1 2 >> swapIf >> print _ >> print",  ["2", "1"], "")
  , ("false 1 2 >> swapIf >> print _ >> print", ["1", "2"], "")
  , ("true 1 2 >> select >> print",  ["1"], "")
  , ("false 1 2 >> select >> print", ["2"], "")
    -- swapIf twice with the same control = id (reversibility)
  , ("true 1 2 >> swapIf >> true ... >> swapIf >> print _ >> print", ["1", "2"], "")
    -- boolean connectives (two Bool wires, cond-dispatched)
  , ("true false >> and >> print",  ["alt2()"], "")
  , ("true true >> and >> print",   ["alt1()"], "")
  , ("false true >> or >> print",   ["alt1()"], "")
  , ("true true >> xor >> print",   ["alt2()"], "")
  , ("true false >> xor >> print",  ["alt1()"], "")
  , ("false true >> implies >> print", ["alt1()"], "")
  , ("true false >> implies >> print", ["alt2()"], "")
  , ("true >> not >> print",        ["alt2()"], "")
    -- folding a sum: row of handlers + generated mergeName / foldName
  , ("data Shape = (Int | Int Int | Int Int Int)\ndef rect = alt2 >> Shape\n3 4 >> rect >> unShape >> (dup >> * | * | + ... >> +) >> mergeShape >> print", ["12"], "")
  , ("data Shape = (Int | Int Int | Int Int Int)\ndef tri = alt3 >> Shape\n1 2 3 >> tri >> [dup >> *] [*] [+ ... >> +] ... >> foldShape >> print", ["6"], "")
    -- multi-wire list literals + matchWith: data-driven first-match guard
  , ("def by3? = (n -> n 3 >> mod >> zero >> (n | n))\n9 [toStr] ([by3?] [drop >> \"fizz\"] >> pack2) >> matchWith >> print", ["fizz"], "")
  , ("def by3? = (n -> n 3 >> mod >> zero >> (n | n))\n7 [toStr] ([by3?] [drop >> \"fizz\"] >> pack2) >> matchWith >> print", ["7"], "")
    -- zip + a fold over flat two-wire elements: the dot product
  , ("(1 2 3 >> pack) (10 20 30 >> pack) >> zip >> [0] [(acc bx -> bx >> unBox >> (a b -> a b >> * >> acc ... >> +))] ... >> foldList >> print", ["140"], "")
    -- arithmetic completeness + negative literals
  , ("7 3 >> div >> print",  ["2"], "")
  , ("15 3 >> mod >> print", ["0"], "")
  , ("-5 >> print",          ["-5"], "")
  , ("-5 3 >> + >> print",   ["-2"], "")
  , ("5 3 >> gt? >> verdict >> print", ["alt1()"], "")
  , ("3 3 >> lte? >> verdict >> print", ["alt1()"], "")
    -- prelude round-out
  , ("5 >> range >> print",  ["list(0, 1, 2, 3, 4)"], "")
  , ("5 >> range >> len >> print", ["5"], "")
  , ("5 >> range >> sum >> print", ["10"], "")
  , ("(2 3 4 >> pack) >> product >> print", ["24"], "")
  , ("(1 3 5 >> pack) >> [odd] ... >> map >> all >> print", ["alt1()"], "")
  , ("(2 4 >> pack) >> [odd] ... >> map >> any >> print", ["alt2()"], "")
  , ("(1 2 3 >> pack) >> [odd?] ... >> map >> partitionSum >> len _ >> print _ >> len >> print", ["2", "1"], "")
  , ("(7 8 >> pack) >> printAll", ["7", "8"], "")
    -- fizzbuzz, the citizenship test
  , ("def fizzbuzz = (n -> (n 15 >> mod >> zero) [\"FizzBuzz\"] [(n 3 >> mod >> zero) [\"Fizz\"] [(n 5 >> mod >> zero) [\"Buzz\"] [n >> toStr] ... >> cond] ... >> cond] ... >> cond)\n15 >> fizzbuzz >> print\n9 >> fizzbuzz >> print\n4 >> fizzbuzz >> print", ["FizzBuzz", "Fizz", "4"], "")
    -- unparse / parse round trip; parse feeds evalCode
  , ("\"dup >> *\" >> parse >> (unparse >> print | print) >> forget", ["dup >> *"], "")
  , ("\"dup >> *\" >> parse >> ((c -> [dup >> *] c (6) >> evalAs >> print) | print) >> forget", ["alt1(36)"], "")
  , ("\"dup >>\" >> parse >> (forget >> 0 >> print | forget >> 1 >> print) >> forget", ["1"], "")
    -- file IO round trip (railway edges)
  , ("\"/tmp/braid-sprint-test.txt\" \"hi\" >> writeFile >> (\"/tmp/braid-sprint-test.txt\" >> readFile >> (print | print) >> forget | print) >> forget", ["hi"], "")
    -- take / skip
  , ("(1 2 3 4 >> pack) >> 2 _ >> take >> print", ["list(1, 2)"], "")
  , ("(1 2 3 4 >> pack) >> 2 _ >> skip >> print", ["list(3, 4)"], "")
  , (".red >> symStr >> \"k=\" ... >> cat >> print", ["k=red"], "")
    -- Code v1: reflect / sections / evalCode / abstraction elimination
  , ("[dup >> *] >> reflect >> ((c -> [dup >> *] c (7) >> evalAs >> print) | print) >> forget", ["alt1(49)"], "")
  , ("[dup >> * >> 1 ... >> +] >> reflect >> ((c -> [dup >> *] (2 c >> take) (6) >> evalAs >> print) | print) >> forget", ["alt1(36)"], "")
  , ("[(x y -> x (2 y >> *) >> +)] >> reflect >> ((c -> [+] c (3) (4) >> evalAs >> print) | print) >> forget", ["alt1(11)"], "")
  , ("[(x y -> y)] >> reflect >> ((c -> [+] c (3) (4) >> evalAs >> print) | print) >> forget", ["alt1(4)"], "")
    -- THE CLOSURE GATE IS LIFTED (stage 5a¾).  `(x -> [x])` is a true
    -- closure; elimination now compiles the quote's body against a copy
    -- of the parameter block laid deepest INSIDE the quote, then binds
    -- the copy off the stack with `capture` — the exponential's two
    -- maps doing what dup/swap/drop cannot.
  , ("[(x -> [x])] >> reflect >> (forget >> 0 >> print | forget >> 1 >> print) >> forget", ["0"], "")
  , ("[(x -> [x])] >> reflect >> ((c -> c >> unparse >> print) | print) >> forget",
     ["dup pass >> _ (_ [dup pass >> drop pass] >> capture) >> drop pass"], "")
    -- one capture per parameter, shallowest-on-the-stack bound first
  , ("[(x -> [x ... >> +])] >> reflect >> ((c -> c >> unparse >> print) | print) >> forget",
     ["dup pass >> _ (_ [dup pass >> _ + >> drop pass] >> capture) >> drop pass"], "")
  , ("[(p q -> [p ... >> ev >> (q ... >> ev | miss) >> merge])] >> reflect >> ((c -> \"two\" >> print) | print) >> forget", ["two"], "")
    -- a capturing ROW: the block is distributed into every track with
    -- `dist2`, each branch drops its own copy, and the row keeps its
    -- original (closed) type
  , ("[(n -> n >> zero >> (n >> drop >> 1 | n n >> *) >> merge)] >> reflect >> ((c -> c >> unparse >> print) | print) >> forget",
     ["dup pass >> _ zero >> dup pass >> _ (dist2 >> (dup pass >> _ drop >> _ 1 >> drop pass | dup pass >> dup pass >> _ swap pass >> _ * >> drop pass)) >> _ merge >> drop pass"], "")
    -- the level-1 library reflects: `lift`, `box`, `whileFn`, `equalsTo`
  , ("[(f -> [_ (f ... >> ev)])] >> reflect >> ((c -> c >> unparse >> print) | print) >> forget",
     ["dup pass >> _ (_ [dup pass >> _ swap pass >> _ _ (dup pass >> _ ev >> drop pass) >> drop pass] >> capture) >> drop pass"], "")
  , ("[(w cd -> [(w) (cd) ... >> evalAs])] >> reflect >> ((c -> \"box\" >> print) | print) >> forget", ["box"], "")
  , ("[(p f -> [p ... >> ev >> (f ... >> ev >> again | done) >> merge])] >> reflect >> ((c -> \"whileFn\" >> print) | print) >> forget", ["whileFn"], "")
  , ("[(k -> [_ k >> equals?])] >> reflect >> ((c -> \"equalsTo\" >> print) | print) >> forget", ["equalsTo"], "")
    -- THE TWO CORNERS 5a3/4 PINNED AS REFUSALS, now positive (5a7/8).
    -- Both emit the GENERATOR `#dist:K` rather than the derived `dist2`:
    -- K is the width of the WRITTEN row, and the residual passes with no
    -- block on it, which is the only thing that can be done with
    -- alternatives nobody can name.
    -- 1. a residual row mentioning a parameter (the prelude's own
    --    `sequence` step is exactly this shape)
  , ("[(r x -> x >> ((y -> r >> (y ... >> cons | ---)) | miss) >> merge)] >> reflect >> ((c -> c >> unparse >> print) | print) >> merge",
     ["_ dup pass >> dup pass >> _ swap pass >> _ _ (dist2 >> (dup pass >> _ swap pass >> _ dup pass >> _ _ (#dist:1 >> (dup pass >> _ cons >> drop pass | ---)) >> _ drop pass >> drop pass | _ miss >> drop pass)) >> _ _ merge >> drop drop pass"], "")
    -- and it RUNS, both on the handled track and through the residual
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [(x s -> s >> (x ... >> + | ---))] >> getCode\n(c) >> unparse >> print\n3 (5 >> alt1) >> [(x s -> s >> (x ... >> + | ---))] (c) ... >> evalAs >> (print | forget) >> merge\n3 (5 >> alt2) >> [(x s -> s >> (x ... >> + | ---))] (c) ... >> evalAs >> (print | forget) >> merge",
     ["_ dup pass >> dup pass >> _ swap pass >> _ _ (#dist:1 >> (dup pass >> _ + >> drop pass | ---)) >> drop drop pass",
      "alt1(8)", "alt2(5)"], "")
    -- 2. a FLAT 3-track row mentioning a parameter: `merge`/`case2` are
    --    binary, but `#dist:3` is not derived from them
  , ("data Shape = (Int | Int Int | Int Int Int)\n[(x s -> s >> unShape >> (drop >> x | drop drop >> x | drop drop drop >> x))] >> reflect >> ((c -> c >> unparse >> print) | print) >> merge",
     ["_ dup pass >> _ _ unShape >> dup pass >> _ swap pass >> _ _ (#dist:3 >> (_ drop >> dup pass >> drop pass | _ drop drop >> dup pass >> drop pass | _ drop drop drop >> dup pass >> drop pass)) >> drop drop pass"], "")
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndata Shape = (Int | Int Int | Int Int Int)\ndef pick = [(x s -> s >> unShape >> (drop >> x | drop drop >> x 100 >> + | drop drop drop >> x 200 >> +) >> mergeShape)]\ndef c = (pick) >> getCode\n9 (7 >> alt1 >> Shape) >> (pick) (c) ... >> evalAs >> (print | forget) >> merge\n9 (7 8 >> alt2 >> Shape) >> (pick) (c) ... >> evalAs >> (print | forget) >> merge\n9 (7 8 1 >> alt3 >> Shape) >> (pick) (c) ... >> evalAs >> (print | forget) >> merge",
     ["9", "109", "209"], "")
    -- `use F` over the `fix` IDIOM: the 5a½ demo that was refused
  , ("def orNil = ((c -> c) | drop ; nil) ; merge\ndef markStage = (s -> \"\\\"after \" (s ; pack ; unparse) ; cat ; _ \"\\\" ... ; print ...\" ; cat ; parse ; orNil)\ndef marked = [(s -> (s ; pack) (s ; markStage) ; append)] ... ; stagewise\nfunctor Traced = marked\ndef fac =\n    use Traced\n    [(self n -> n >> zero? >> ((z -> 1) | (m -> m (m 1 >> - >> self ... >> ev) >> *)) >> merge)] ...\n    fix ...\n    ev\n4 >> fac >> print",
     ["after [_ dup pass >> _ _ zero? >> dup pass >> _ swap pass >> _ _ (dist2 >> (_ _ 1 >> _ drop pass >> drop pass | _ dup pass >> _ dup pass >> _ _ swap pass >> dup pass >> _ swap pass >> _ _ swap pass >> _ _ _ (_ dup pass >> _ _ _ 1 >> _ _ - >> dup pass >> _ swap pass >> _ _ ev >> _ drop pass >> drop pass) >> _ _ * >> _ drop pass >> drop pass)) >> _ _ merge >> drop drop pass] pass",
      "after fix pass", "after ev", "24"], "")
    -- and over a capturing QUOTE, where the emitted word is `capture`
  , ("def orNil = ((c -> c) | drop ; nil) ; merge\ndef markStage = (s -> \"\\\"after \" (s ; pack ; unparse) ; cat ; _ \"\\\" ... ; print ...\" ; cat ; parse ; orNil)\ndef marked = [(s -> (s ; pack) (s ; markStage) ; append)] ... ; stagewise\nfunctor Traced = marked\ndef adder =\n    use Traced\n    (n -> [n ... >> +])\n7 >> adder >> _ 5 >> ev >> print",
     ["after dup pass", "after _ (_ [dup pass >> _ + >> drop pass] >> capture)", "after drop pass", "12"], "")
    -- dist2/undist2 are inverse at sample points
  , ("7 (5 >> alt1) >> dist2 >> (+ | -) >> merge >> print", ["12"], "")
  , ("7 (5 >> alt2) >> dist2 >> (+ | -) >> merge >> print", ["2"], "")
  , ("7 5 >> alt1 >> undist2 >> dist2 >> (+ | -) >> merge >> print", ["12"], "")
  , ("7 5 >> alt2 >> undist2 >> dist2 >> (+ | -) >> merge >> print", ["2"], "")
  , ("7 (5 >> alt1) >> dist2 >> undist2 >> _ merge >> + >> print", ["12"], "")
  , ("7 (5 >> alt1) >> _ merge >> + >> print", ["12"], "")
    -- partial application, the derived word elimination emits
  , ("7 [+] >> capture >> _ 5 >> ev >> print", ["12"], "")
  , ("[+] >> curry >> _ 7 >> ev >> _ 5 >> ev >> print", ["12"], "")
    -- evalCode dynamic check: + on one wire misses, evidence kept
  , ("[+] >> reflect >> ((c -> [dup >> *] c (5) >> evalAs >> (forget >> 0 | forget >> 1) >> merge >> print) | forget >> 2 >> print) >> forget", ["1"], "")
    -- THE SANDBOX: a pure witness refuses io code — by skolemizing the
    -- effect tail, not by accident (before that, absorption let io
    -- code raise the tail, and the refusal only happened when the two
    -- inference runs reused a tail name and tripped the occurs check)
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\n[_] ([dup >> print ...] >> getCode) (5) >> evalAs >> (print | print forget) >> merge", ["Cannot unify effects: IO vs pure (the expected type fixes the grade; this code must stay pure)"], "")
    -- ...an io witness permits io, and admits pure code too
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\n[dup >> print ...] ([dup >> print ...] >> getCode) (5) >> evalAs >> (print | print forget) >> merge\n[dup >> print ...] ([_] >> getCode) (6) >> evalAs >> (print | print forget) >> merge", ["5", "5", "6"], "")
    -- GLA: transpose of add is copy; linearity checked over reflected code
  , ("def dualSym = (s -> (s .dup >> equals) [.+] [(s .+ >> equals) [.dup] [s] ... >> cond] ... >> cond)\ndef dualAtom = [(s -> s >> dualSym >> alt1 >> Atom)] [(n -> n >> alt2 >> Atom)] [(t -> t >> alt3 >> Atom)] [(y -> y >> alt4 >> Atom)] [(c -> c >> alt5 >> Atom)] [(l b -> l b >> alt6 >> Atom)] [(c -> c >> alt7 >> Atom)] ... >> foldAtom\ndef transposeC = reverse >> [[dualAtom] ... >> map] ... >> map\n[+] >> reflect >> ((c -> [dup] (c >> transposeC) (5) >> evalAs >> print) | print) >> forget", ["alt1(5, 5)"], "")
    -- matrices as diagrams: composition is matmul ([[1,2],[3,4]] squared)
  , ("def m = (x y -> x (2 y >> *) >> + >> _ ((3 x >> *) (4 y >> *) >> +))\n1 0 >> m >> m >> toStr _ >> _ toStr >> cat >> print", ["715"], "")
    -- split-ev-combine: dup broadcasts, filters split, folds ev
  , ("def sumL = [+] 0 ... >> fold\n(1 2 3 4 >> pack) >> dup >> ([odd?] ... >> filter >> sumL) _ >> _ ([even?] ... >> filter >> sumL) >> + >> print", ["10"], "")
    -- the list monad, all derived in the prelude:
    -- single = return, concat = join, flatMap = bind, filter via bind
  , ("(1 2 3 >> pack) >> reverse >> print", ["list(3, 2, 1)"], "")
  , ("(1 2 >> pack) (3 4 >> pack) >> append >> print", ["list(1, 2, 3, 4)"], "")
  , ("((1 2 >> pack) nil (3 >> pack) >> pack) >> concat >> print", ["list(1, 2, 3)"], "")
  , ("5 >> single >> print", ["list(5)"], "")
  , ("(1 2 3 4 >> pack) >> [odd?] ... >> filter >> print", ["list(1, 3)"], "")
  , ("(1 2 3 >> pack) >> [dup >> _ single >> cons] ... >> flatMap >> print", ["list(1, 1, 2, 2, 3, 3)"], "")
    -- one generic reduction, two Monoid models (dictionaries as wires)
  , ("(1 2 3 4 >> pack) >> [+] 0 ... >> fold >> print", ["10"], "")
  , ("((1 2 >> pack) (3 >> pack) nil >> pack) >> [append] nil ... >> fold >> print", ["list(1, 2, 3)"], "")
    -- chunked fold + combine = whole fold (associativity licenses
    -- parallel reduce)
  , ("def w = (1 2 3 4 5 6 >> pack) >> [*] 1 ... >> fold\ndef l = (1 2 3 >> pack) >> [*] 1 ... >> fold\ndef r = (4 5 6 >> pack) >> [*] 1 ... >> fold\nw >> _ (l >> _ r >> *) >> eq? >> verdict >> print", ["alt1()"], "")
    -- laws as programs, presentations as enumerators
  , ("def xs = (0 1 2 3 >> pack)\nxs >> [(1 ... >> +) >> (2 _ >> *)] ... >> map >> _ (xs >> [(2 _ >> *) >> (1 ... >> +) >> (1 ... >> +)] ... >> map) >> eq? >> verdict >> print", ["alt1()"], "")
  , ("def xs = (0 1 2 3 >> pack)\nxs >> [(1 ... >> +) >> (2 _ >> *)] ... >> map >> _ (xs >> [(2 _ >> *) >> (1 ... >> +)] ... >> map) >> eq? >> verdict >> print", ["alt2()"], "")
    -- multi-line kleisli: newline absorption around >=> (either side)
  , ("def double2 = 2 _ >> *\ndef process =\n    even?\n    >=> _ 100 >> less?\n    >=> double2 >> ok\n120 >> process >> print", ["alt2(120)"], "")
  , ("0 >> (even? >=>\nzero?) >> print", ["alt1(0)"], "")
    -- cleanup-baked comparison routers and quoted sections: predicates
    -- built inline, no lambda, no factory
  , ("def equals = eq? >> (_ drop | _ drop)\n5 >> _ 5 >> equals? >> print", ["alt1(5)"], "")
  , ("def both = (p q -> [p ... >> ev >> (q ... >> ev | alt2) >> merge])\n5 >> ([_ 5 >> equals?] [odd?] >> both) ... >> ev >> print", ["alt1(5)"], "")
  , ("def equals = eq? >> (_ drop | _ drop)\ndef both = (p q -> [p ... >> ev >> (q ... >> ev | alt2) >> merge])\n6 >> ([_ 5 >> equals?] [odd?] >> both) ... >> ev >> print", ["alt2(6)"], "")
  , ("def less = lt? >> (_ drop | _ drop)\ndef whileFn = (p f -> [p ... >> ev >> (f ... >> ev >> again | done) >> merge])\ndef while = whileFn ... >> loop\ndef double = 2 _ >> *\n7 >> [_ 100 >> less?] [double] ... >> while >> print", ["112"], "")
    -- user-built predicates: scaffold-test-cleanup, and factories that
    -- return quoted routers
  , ("def five? = _ 5 >> eq? >> (_ drop | _ drop)\n5 >> five? >> print", ["alt1(5)"], "")
  , ("def equalsK = (k -> [_ k >> eq? >> (_ drop | _ drop)])\n7 >> (5 >> equalsK) ... >> ev >> print", ["alt2(7)"], "")
  , ("def equalsK = (k -> [_ k >> eq? >> (_ drop | _ drop)])\n5 >> (5 >> equalsK) ... >> ev >> print", ["alt1(5)"], "")
  , ("def whileFn = (p f -> [p ... >> ev >> (f ... >> ev >> again | done) >> merge])\ndef while = whileFn ... >> loop\ndef lessThan = (k -> [_ k >> lt? >> (_ drop | _ drop)])\ndef double = 2 _ >> *\n7 >> (100 >> lessThan) [double] ... >> while >> print", ["112"], "")
    -- value-level predicate combinators: negate/both/either on quoted
    -- routers (closures assemble the composed router)
  , ("def negate = (p -> [p ... >> ev >> (alt2 | alt1) >> merge])\ndef both = (p q -> [p ... >> ev >> (q ... >> ev | alt2) >> merge])\ndef either = (p q -> [p ... >> ev >> (alt1 | q ... >> ev) >> merge])\ndef small? = _ 10 >> lt? >> (_ drop | _ drop)\n4 >> ([even?] [small?] >> both) ... >> ev >> print", ["alt1(4)"], "")
  , ("def negate = (p -> [p ... >> ev >> (alt2 | alt1) >> merge])\ndef both = (p q -> [p ... >> ev >> (q ... >> ev | alt2) >> merge])\ndef either = (p q -> [p ... >> ev >> (alt1 | q ... >> ev) >> merge])\ndef small? = _ 10 >> lt? >> (_ drop | _ drop)\n40 >> ([even?] [small?] >> both) ... >> ev >> print", ["alt2(40)"], "")
  , ("def negate = (p -> [p ... >> ev >> (alt2 | alt1) >> merge])\ndef both = (p q -> [p ... >> ev >> (q ... >> ev | alt2) >> merge])\ndef either = (p q -> [p ... >> ev >> (alt1 | q ... >> ev) >> merge])\ndef small? = _ 10 >> lt? >> (_ drop | _ drop)\n7 >> ([even?] [small?] >> both) ... >> ev >> print", ["alt2(7)"], "")
  , ("def negate = (p -> [p ... >> ev >> (alt2 | alt1) >> merge])\ndef both = (p q -> [p ... >> ev >> (q ... >> ev | alt2) >> merge])\ndef either = (p q -> [p ... >> ev >> (alt1 | q ... >> ev) >> merge])\ndef small? = _ 10 >> lt? >> (_ drop | _ drop)\n3 >> ([even?] [small?] >> either) ... >> ev >> print", ["alt1(3)"], "")
  , ("def negate = (p -> [p ... >> ev >> (alt2 | alt1) >> merge])\ndef both = (p q -> [p ... >> ev >> (q ... >> ev | alt2) >> merge])\ndef either = (p q -> [p ... >> ev >> (alt1 | q ... >> ev) >> merge])\ndef small? = _ 10 >> lt? >> (_ drop | _ drop)\n9 >> ([even?] [small?] >> both >> negate) ... >> ev >> print", ["alt1(9)"], "")
    -- until = while of the negated predicate, all in-language
  , ("def whileFn = (p f -> [p ... >> ev >> (f ... >> ev >> again | done) >> merge])\ndef while = whileFn ... >> loop\ndef negate = (p -> [p ... >> ev >> (alt2 | alt1) >> merge])\ndef until = (p f -> (p >> negate) f) ... >> while\ndef big? = _ 100 >> lt? >> (_ drop | _ drop) >> (alt2 | alt1) >> merge\ndef double = 2 _ >> *\n7 >> [big?] [double] ... >> until >> print", ["112"], "")
    -- router boolean algebra: not = track swap; and/or = one-sided rows
  , ("5 >> odd? >> (alt2 | alt1) >> merge >> print",  ["alt2(5)"], "")
  , ("0 >> even? >> (zero? | alt2) >> merge >> print", ["alt1(0)"], "")
  , ("6 >> even? >> (zero? | alt2) >> merge >> print", ["alt2(6)"], "")
  , ("2 >> even? >> (alt1 | zero?) >> merge >> print", ["alt1(2)"], "")
  , ("7 >> even? >> (alt1 | zero?) >> merge >> print", ["alt2(7)"], "")
    -- Euclid's subtractive gcd: router negation is a track swap
  , ("def whileFn = (p f -> [p ... >> ev >> (f ... >> ev >> again | done) >> merge])\ndef while = whileFn ... >> loop\ndef not = (alt2 | alt1) >> merge\ndef neq? = eq? >> not\ndef shrink = lt? >> (swap | ---) >> merge >> _ dup >> - ...\n48 18 >> [neq?] [shrink] ... >> while >> drop ... >> print", ["6"], "")
  , ("def whileFn = (p f -> [p ... >> ev >> (f ... >> ev >> again | done) >> merge])\ndef while = whileFn ... >> loop\ndef not = (alt2 | alt1) >> merge\ndef neq? = eq? >> not\ndef shrink = lt? >> (swap | ---) >> merge >> _ dup >> - ...\n1071 462 >> [neq?] [shrink] ... >> while >> drop ... >> print", ["21"], "")
    -- recursion: tail recursion replaces the loop harness; tree recursion is new
  , ("def lt100? = _ 100 >> lt? >> (_ drop | _ drop)\ndef double = 2 _ >> *\ndef until100 = [(self ... -> lt100? >> (double >> self ... >> ev | _) >> merge)] ... >> fix ... >> ev\n7 >> until100 >> print", ["112"], "")
  , ("def decr = _ 1 >> -\ndef sumTo = [(self a n -> n >> zero? >> ((z -> a) | (m -> (a m >> +) (m >> decr) >> self ... >> ev)) >> merge)] ... >> fix ... >> ev\n0 5 >> sumTo >> print", ["15"], "")
  , ("def decr = _ 1 >> -\ndef lt2? = _ 2 >> lt? >> (_ drop | _ drop)\ndef fib = [(self ... -> lt2? >> (_ | (n -> n >> decr >> self ... >> ev >> _ (n 2 >> - >> self ... >> ev) >> +)) >> merge)] ... >> fix ... >> ev\n10 >> fib >> print", ["55"], "")
  , ("5 >> (_ 2 >> -) >> print",           ["3"],  "")
  , ("2 2 >> eq?",                         [],     "alt1(2, 2)")
  , ("3 5 >> lt?",                         [],     "alt1(3, 5)")
  , ("(1 2 >> pack) >> uncons",               [],     "list(1, 2)")
  , ("nil >> uncons",                   [],     "alt1()")
    -- deferred peel builds a nested sum; case(…) folds the whole spine
  , ("def classify = negative? >> (drop >> \"neg\" | pass) >> (pass | zero?) >> [pass] [drop >> \"zero\"] [toStr] ... >> case3\n-4 >> classify >> print\n0 >> classify >> print\n7 >> classify >> print", ["neg", "zero", "7"], "")
    -- associator round-trip is identity on the routed value
  , ("def tag = negative? >> (drop >> \"neg\" | pass) >> (pass | zero?)\n5 >> tag >> assocL >> assocR >> [pass] [drop >> \"zero\"] [toStr] ... >> case3 >> print", ["5"], "")
    -- guard ladder words: bound subject, bare Bool conditions, answers
    -- as plain values; if opens, elif probes while undecided, else /
    -- otherwise (lazy, quoted) close.  One guard per line, constant _.
  , ("def sign = x -> (x >> negative) \"neg\" >> if >> _ (x >> zero) \"zero\" >> elif >> _ (x >> toStr) >> else\n-4 >> sign >> print\n0 >> sign >> print\n7 >> sign >> print", ["neg", "zero", "7"], "")
  , ("def grade = x -> (89 x >> less) \"A\" >> if >> _ (79 x >> less) \"B\" >> elif >> _ (69 x >> less) \"C\" >> elif >> _ [\"F\"] >> otherwise\n95 >> grade >> print\n85 >> grade >> print\n75 >> grade >> print\n50 >> grade >> print", ["A", "B", "C", "F"], "")
    -- lane accumulation: each `...` line pushes a (cond, answer) pair
    -- UNDER the product; decide folds — first-written true lane wins
  , ("def sign =\n    x ->\n    (x >> negative) \"neg\" ...\n    (x >> zero) \"zero\" ...\n    (x >> toStr) ...\n    decide\n-4 >> sign >> print\n0 >> sign >> print\n7 >> sign >> print", ["neg", "zero", "7"], "")
  , ("def grade =\n    x ->\n    (89 x >> less) \"A\" ...\n    (79 x >> less) \"B\" ...\n    (69 x >> less) \"C\" ...\n    \"F\" ...\n    decide\n95 >> grade >> print\n85 >> grade >> print\n50 >> grade >> print", ["A", "B", "F"], "")
    -- routing form: the router's hit value flows into the action
  , ("def cl = _ [odd?] [dup >> *] >> ifRoute >> _ [negative?] [drop >> 0] >> elifRoute >> _ [pass] >> otherwise\n7 >> cl >> print\n-4 >> cl >> print\n6 >> cl >> print", ["49", "0", "6"], "")
    -- aligned track-columns: | no longer absorbs newlines, so each line
    -- is one complete row (pass sugar fills the empty arm) and the rows
    -- compose by newline-as->>.  Two rows here == the row (dup>>* | 1..+).
  , ("5 >> alt1\ndup >> * | pass\npass     | 1 ... >> +\nmerge >> print", ["25"], "")
    -- bare rows, line-scoped
  , ("5 >> alt1\ndup | +\n+ | id\nmerge >> (x -> x 1 >> +)\nprint",  ["11"], "")
  , ("3 4 >> alt2\ndup | +\n+ | id\nmerge >> (x -> x 1 >> +)\nprint", ["8"], "")

    -- match2 as a DERIVED definition (spec: match = row of applies + merge)
  , ("def match2 = (f g s -> s >> (f ... >> ev | g ... >> ev) >> merge)\n5 >> alt1 >> [dup >> *] [1 ... >> +] ... >> match2 >> print",
                                           ["25"], "")

    -- lists: the spec's sum-of-squares program
  , ("(1 2 3 >> pack)",                  [],     "list(1, 2, 3)")   -- display keeps list(…)
  , ("[dup >> *] (1 2 3 4 5 >> pack)\nmap\n[+] 0 id\nfold\nprint",
                                           ["55"], "")
    -- foldExp at three widths through ONE polymorphic def (n erased;
    -- the runtime segment width is the witness), including n = 0
  , ("1 2 3 >> [+] 0 ... >> foldExp >> print", ["6"], "")
  , ("def total = [+] 0 ... >> foldExp\n1 2 3 4 5 >> total >> print", ["15"], "")
  , ("def total = [+] 0 ... >> foldExp\n10 20 >> total >> print\ntotal >> print", ["30", "0"], "")
  , ("def biggest = [(a x -> a x >> lt? >> ((p q -> q) | (p q -> p)) >> merge)] 0 ... >> foldExp\n3 9 4 >> biggest >> print", ["9"], "")
    -- GLA: pointwise ops on bundles; the linear 2n = w case resolves
    -- addN/zipN against concrete stacks
  , ("1 2 3 >> dupN >> addN >> sumN >> print", ["12"], "")
  , ("1 2 3 10 20 30 >> addN >> sumN >> print", ["66"], "")
  , ("2 1 2 3 >> scaleN >> sumN >> print", ["12"], "")
    -- the bialgebra check, operationally: copy-then-add = scale-by-2
  , ("def dbl = dupN >> addN\ndef dblS = 2 ... >> scaleN\n20 30 >> dbl >> sumN >> print\n20 30 >> dblS >> sumN >> print", ["100", "100"], "")
  , ("def dot = zipN >> [(acc a b -> (a b >> *) acc >> +)] 0 ... >> foldExp2\n1 2 3 4 5 6 >> dot >> print", ["32"], "")
    -- firstTrue: guard lanes as a bare product, first true wins
  , ("def sign = x -> [x >> toStr] (x >> negative) [\"neg\"] (x >> zero) [\"zero\"] >> firstTrue\n-4 >> sign >> print\n0 >> sign >> print\n7 >> sign >> print", ["neg", "zero", "7"], "")
    -- cut soundness: at stage boundaries, run(prefix) ; run(suffix) =
    -- run(whole) — the concatenative property at spine granularity
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [1 2 >> + >> dup >> *] >> getCode\ndef cutAt =\n    pre suf k ->\n    (pre) (k c >> take) >> evalAs\n    ((suf) (k c >> skip) ... >> evalAs >> (print | forget) >> merge | forget) >> merge\n[pass] [1 2 >> + >> dup >> *] 0 >> cutAt\n[1 2] [+ >> dup >> *] 1 >> cutAt\n[1 2 >> + >> dup] [*] 3 >> cutAt", ["9", "9", "9"], "")
    -- vertical cuts: atom slices within a stage are runnable sub-tensors
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef s0 = ([1 2 >> +] >> getCode) >> uncons >> (nil | (s r -> s)) >> merge\n[1] (1 s0 >> take >> single) >> evalAs >> (print | forget) >> merge\n[2] (1 s0 >> skip >> single) >> evalAs >> (print | forget) >> merge", ["1", "2"], "")
    -- box: Code -> Fn without running; the check fires at ev.
    -- Deferring the RUN costs the result's TYPE: what boxed code returns
    -- is discovered when it runs, so the hit track is existential and a
    -- caller must stay parametric (`forget`, not `print`).
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\n[0] (2 ([1 2 >> + >> dup >> *] >> getCode) >> take) >> box\nev >> (forget >> \"ran\" | pass) >> merge >> print", ["ran"], "")
    -- a splice whose code produces the WRONG WIDTH now rides the miss
    -- track (it used to reach the top-level backstop as "result desync")
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [1 2] >> getCode\n[0] (c) ... >> evalAs >> (print | forget) >> merge", [], "")
    -- …and the wrong TYPE at the right width, likewise: this is the
    -- smuggle the hole allowed — a Str reaching a List(Int)
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\n[0] ([ \"hi\" ] >> getCode) >> evalAs\n((x -> 1 x >> pack) | drop >> nil) >> merge\n[toStr] ... >> map >> print", ["alt1()"], "")
    -- pack builds the same value as the list(…) literal; pack2 makes
    -- two-wire elements; the empty pack is nil
  , ("def a = 1 (2 (3 nil >> cons) >> cons) >> cons\ndef b = (1 2 3 >> pack)\na >> _ b >> eq? >> verdict >> print", ["alt1()"], "")
  , ("(1 2 3 >> pack) >> sum >> print\n(pack) >> len >> print", ["6", "0"], "")
  , ("(1 10 2 20 >> pack2) >> [0] [(acc bx -> bx >> unBox >> (a b -> (a b >> *) acc >> +))] ... >> foldList >> print", ["50"], "")
  , ("def fanout = [(x -> (x (10 x >> *) >> pack))]\nfanout 7 >> ev >> print", ["list(7, 70)"], "")
    -- EARLY BINDING: shadowing a prelude ingredient (equals, here forced
    -- always-true) must NOT leak into the derived prelude word odd? that
    -- was typechecked against the original.  odd? classifies 4 as even
    -- via the REAL equals; the direct call sees the shadow.  (Late
    -- binding would print "odd" then "eq".)
  , ("def equals = drop drop >> true\n4 >> odd? >> (drop >> \"odd\" | drop >> \"even\") >> merge >> print\n2 3 >> equals >> (\"eq\" | \"neq\") >> merge >> print", ["even", "eq"], "")
    -- CLOSURE CAPTURE: a quote written in user scope carries that scope,
    -- so when a prelude combinator (map) applies it, the user def dbl
    -- resolves — even though map's own scope never saw dbl.
  , ("def dbl = 2 _ >> *\n(1 2 3 >> pack) >> [dbl] ... >> map >> print", ["list(2, 4, 6)"], "")
    -- open binders at runtime: the remainder is handed TO the body, so
    -- the body positions it (unlike `(x -> body) ...`, which routes it
    -- around).  1 1 2 3 -> 2 5 -> 7.
  , ("1 2 3 >> (x ... -> x x ... >> + + >> +) >> print", ["7"], "")
  , ("1 2 >> (x _ -> x x _ >> + _ >> +) >> print", ["4"], "")
  , ("1 2 3 4 >> (a b ... -> a b ... >> + +) >> print print", ["3", "7"], "")
  , ("1 2 3 >> (x _ z -> z _ x) >> print print print", ["3", "2", "1"], "")
    -- reflection: a binder with `_` slots compiles to pure wiring; check
    -- the ROUND-TRIP VALUE, not merely that reflection succeeded (a
    -- success-only test let a wrong permutation ship once)
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [x _ -> x _] >> getCode\n7 8 >> [x _ -> x _] (c) ... >> evalAs >> (print print | forget) >> merge", ["7", "8"], "")
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [x _ -> x x _ >> + _ >> +] >> getCode\n1 2 >> [x _ -> x x _ >> + _ >> +] (c) ... >> evalAs >> (print | forget) >> merge", ["4"], "")
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [x _ z -> z _ x] >> getCode\n1 2 3 >> [x _ z -> z _ x] (c) ... >> evalAs >> (print print print | forget) >> merge", ["3", "2", "1"], "")
    -- OPEN binders eliminate too.  The param block is the DEEPEST
    -- segment (a resource for the body's duration), so the erased
    -- passthrough rides above everything and every fetch crosses only
    -- the static prefix of its own stage.  Round-trip the VALUE — a
    -- success-only test would miss a wrong permutation.
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [x ... -> x ...] >> getCode\n7 >> [x ... -> x ...] (c) ... >> evalAs >> (print | forget) >> merge", ["7"], "")
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [x _ y ... -> y _ x ...] >> getCode\n1 2 3 >> [x _ y ... -> y _ x ...] (c) ... >> evalAs >> (print print print | forget) >> merge", ["3", "2", "1"], "")
    -- ...including a body that consumes OUT of the passthrough (this
    -- one returned 9 instead of 7 under an earlier layout)
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [x ... -> x x ... >> + + >> +] >> getCode\n1 2 3 >> [x ... -> x x ... >> + + >> +] (c) ... >> evalAs >> (print | forget) >> merge", ["7"], "")
    -- OPEN-ARITY atoms in a binder body: injections, merge, an open
    -- group.  They eat upward from where they stand and the block sits
    -- below them, so nothing needs a width — a parameter fetched AFTER
    -- them included.  (Rejected outright under the params-on-top layout.)
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [x -> x >> alt1] >> getCode\n7 >> [x -> x >> alt1] (c) ... >> evalAs >> (print | forget) >> merge", ["alt1(7)"], "")
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [a b -> a b >> eq? >> (forget >> 1 | forget >> 0) >> merge] >> getCode\n3 3 >> [a b -> a b >> eq? >> (forget >> 1 | forget >> 0) >> merge] (c) ... >> evalAs >> (print | forget) >> merge\n3 4 >> [a b -> a b >> eq? >> (forget >> 1 | forget >> 0) >> merge] (c) ... >> evalAs >> (print | forget) >> merge", ["1", "0"], "")
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [x _ -> dup >> alt1 >> (forget >> 1 | forget >> 0) >> merge >> _ x >> +] >> getCode\n5 6 >> [x _ -> dup >> alt1 >> (forget >> 1 | forget >> 0) >> merge >> _ x >> +] (c) ... >> evalAs >> (print | forget) >> merge", ["6"], "")
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [x ... -> x ... >> alt2 >> (forget >> 0 | +) >> merge] >> getCode\n1 2 >> [x ... -> x ... >> alt2 >> (forget >> 0 | +) >> merge] (c) ... >> evalAs >> (print | forget) >> merge", ["3"], "")
    -- the naming binder is an open binder, so it reflects as wiring too
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [-> x -> x ... >> * ...] >> getCode\n7 >> [-> x -> x ... >> * ...] (c) ... >> evalAs >> (print | forget) >> merge", ["49"], "")
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [-> x -> drop >> x ...] >> getCode\n9 >> [-> x -> drop >> x ...] (c) ... >> evalAs >> (print | forget) >> merge", ["9"], "")
    -- CODATA: an infinite stream, forced one cell at a time. Fn in the
    -- data declaration makes the thunked tail expressible; productive
    -- corecursion (from) is guarded by the quote.
  , ("data Stream(a) = (a Fn⟨• =Recursive> Stream(a)⟩)\ndef headS = unStream >> (h t -> h)\ndef tailS = unStream >> (h t -> t) >> ev\ndef from = [(self n -> n [n 1 >> + >> self ... >> ev] >> Stream)] ... >> fix ... >> ev\n0 >> from >> tailS >> tailS >> headS >> print", ["2"], "")
    -- vertical track-columns: flat 3-sum via inject-and-collapse, then
    -- bare rows each touching one track (empty arms pass)
  , ("def route3 = negative? >> (alt1 | zero? >> (alt2 | alt3) >> merge) >> merge\ndef describe =\n    route3\n    drop >> \"neg\" | |\n    | drop >> \"zero\" |\n    | | toStr\n    (print | print | print)\n    forget\n-4 >> describe\n0 >> describe\n7 >> describe", ["neg", "zero", "7"], "")
    -- STAGE 4½: the receipt is a STAGE, so it reflects with the code it
    -- was minted onto, and code that carries a label needs a witness
    -- that carries it too — the sandbox reads provenance exactly as it
    -- reads io
  , (idF ++ "def q = [use Same >> dup >> *]\nq >> getCode >> unparse >> print",
     ["use@Same >> dup >> *"], "")
  , (idF ++ "def q = [use Same >> dup >> *]\n[use Same >> dup >> *] (q >> getCode) (6) >> evalAs >> (print | print forget) >> merge",
     ["36"], "")
  , (idF ++ "def q = [use Same >> dup >> *]\n[dup >> *] (q >> getCode) (6) >> evalAs >> (print | print forget) >> merge",
     ["Cannot unify effects: Same vs pure (the expected type fixes the grade; this code must stay pure)"], "")

    -- TEMPLATES run: one body, two models, two answers
  , (tmplMod ++ "def total  = use IntSum ; fold1\n\
     \def joined = use StrCat ; fold1\n\
     \1 2 3 4 ; total ; print\n\
     \\"a\" \"b\" \"c\" ; joined ; print", ["10", "abc"], "")
    -- a template calling a template, at both models
  , (tmplMod ++ "def a = use IntSum ; quad\ndef b = use StrCat ; quad\n\
     \5 ; a ; print\n\"z\" ; b ; print", ["20", "zzzz"], "")
    -- a template is expanded where it LANDS: a resource scope between
    -- the model and the call routes the expanded body too
  , (tmplMod ++ "resource Log = Str\ndef note = unLog _ ; cat ; Log\n\
     \def p =\n    use IntSum\n    use Log\n    twice\n    \"done\"\n    note\n\
     \(\"\" ; Log) 3 ; p ; unLog _ ; print ... ; print", ["done", "6"], "")
    -- the handler discharges the resource and the program runs
  , (handlerMod ++ "def square =\n    use Log\n    dup ; *\n    \"squared \"\n    note\n\
     \[square] ; collectLog ; _ 7 ; ev\nprint print",
     ["squared ", "49"], "")
    -- the generic handler, at the resource its model names
  , (collectorMod ++ "def bump = unCounter ; 1 ... ; + ; Counter\n\
     \def tick =\n    use Counter\n    dup ; *\n    bump\n\
     \def collectCount = use Counts ; collected\n\
     \[tick] ; collectCount ; _ 7 ; ev\nprint print", ["1", "49"], "")

    -- STAGE 5b: RULE SETS.  `model Opt : Base = p = q` declares a word
    -- `Opt : Code ⇒ Code` and a functor of the same name; `use Opt`
    -- applies it atomwise and mints `=Opt>`.  The rule itself is
    -- blessed ONCE, at the declaration, by `subsumes` — unification
    -- blesses a call, subsumption blesses a rule.
  , (ruleMod ++ "def p =\n    use Opt\n    dupInt\n    +\n5 >> p >> print", ["10"], "")
    -- the inline and the block form declare the same set
  , ("def dupInt = dup >> _ _ 0 >> _ +\ndef twice = dup >> +\ndef double = 2 _ >> *\n\
     \model Opt : Base\n    dupInt = dup\n    twice = double\n\
     \def p =\n    use Opt\n    dupInt\n    +\n5 >> p >> print", ["10"], "")
    -- a rule fires inside a QUOTATION: the engine recurses into quotes,
    -- rows (residual flag carried) and groups
  , (ruleMod ++ "def mapped =\n    use Opt\n    [dupInt >> +] ... >> map\n\
     \(1 2 3 >> pack) >> mapped >> print", ["list(2, 4, 6)"], "")
    -- ... and therefore into a `fix` body, where the recursion lives
  , (ruleMod ++ "def sumTo =\n    use Opt\n\
     \    [(self a n -> n >> dupInt >> drop _ >> zero? >> ((z -> a) | (m -> (a m >> +) (m >> _ 1 >> -) >> self ... >> ev)) >> merge)] ...\n\
     \    fix ...\n    ev\n0 5 >> sumTo >> print", ["15"], "")
    -- a row, and a RESIDUAL row, both rewrite
  , (ruleMod ++ "data Case(---) = (Int | ---)\n\
     \def bump = use Opt ; unCase ; (dupInt ; + | ---) ; Case\n\
     \(3 >> alt1 >> Case) >> bump >> unCase >> (pass | forget >> 0) >> merge >> print",
     ["6"], "")
    -- a PURE replacement under an IO pattern passes: ∅ is the bottom of
    -- the grade semilattice, so subeffecting comes free with `subsumes`
  , ("def noisy = toStr >> print\ndef quiet = drop\nmodel G : Base = noisy = quiet\n\
     \def prog =\n    use G\n    noisy\n\"ran\" >> print\n5 >> prog", ["ran"], "")
    -- `lift2` applies the same word at RUNTIME, with the program as its
    -- own witness and its own fallback
  , (ruleMod ++ "[Opt] [dupInt >> +] >> lift2 >> _ 5 >> ev >> print", ["10"], "")
    -- a hand-rolled table CAN narrow (nothing blessed it), and then the
    -- witness refuses the rewrite and the original runs
  , ("def two = drop 1 1\n\
     \def narrow = (c -> (.two >> pack) (.dup >> pack) c >> rewrite)\n\
     \[narrow] [two >> +] >> lift2 >> _ \"the original ran\" >> ev >> print",
     ["2"], "")

    -- STAGE 5b: `sameCodeC`.  Code has already been through abstraction
    -- elimination, so it DECIDES what `sameCode` refuses for carrying a
    -- binder — `[(x -> x x)]` and `[dup]` are the same morphism.
  , ("def v = (\"same\" | \"differ\") >> merge\n\
     \([(x -> x x)] >> getCode) ([dup] >> getCode) >> sameCodeC >> v >> print\n\
     \([(a b -> b a)] >> getCode) ([swap] >> getCode) >> sameCodeC >> v >> print\n\
     \([dup >> _ dup] >> getCode) ([dup >> dup _] >> getCode) >> sameCodeC >> v >> print\n\
     \([toStr >> dup] >> getCode) ([dup >> toStr _] >> getCode) >> sameCodeC >> v >> print",
     ["same", "same", "same", "differ"], "")
    -- a functor law, decided: F(id) = id and F(p;q) = F(p);F(q) for a
    -- rule set (composition of Code is `append`)
  , (ruleMod ++ "def v = (\"holds\" | \"fails\") >> merge\n\
     \(nil >> Opt) nil >> sameCodeC >> v >> print\n\
     \((([dupInt] >> getCode) ([twice] >> getCode) >> append) >> Opt) \
     \((([dupInt] >> getCode >> Opt) ([twice] >> getCode >> Opt)) >> append) >> sameCodeC >> v >> print",
     ["holds", "holds"], "")
    -- IDEMPOTENCE as a functor law, and IMAGE MEMBERSHIP as a program
    -- assertion: two different kinds of claim, the second meaningful
    -- only because the first holds
  , (ruleMod ++ "def v = (\"yes\" | \"no\") >> merge\n\
     \def s = [twice >> dupInt >> +] >> getCode\n\
     \(s >> Opt >> Opt) (s >> Opt) >> sameCodeC >> v >> print\n\
     \([double] >> getCode >> Opt) ([double] >> getCode) >> sameCodeC >> v >> print\n\
     \([twice] >> getCode >> Opt) ([twice] >> getCode) >> sameCodeC >> v >> print",
     ["yes", "yes", "no"], "")
    -- the laws as a THEORY, audited at module start: a model that
    -- fails one stops the module before main runs
  , (ruleMod ++ optimizerTheory ++ "model OptIsOpt : Optimizer\n\
     \    ap     = Opt\n    sample = [twice >> dupInt >> +] >> getCode\n\"audited\" >> print",
     ["audited"], "")
    -- A TRANSFORMATION accepted: the squares are checked at declaration time
    -- and the component is an ordinary word under its own name, usable
    -- in a def that was written before the declaration.
  , (monoidMod ++ "transformation Len : ListMonoid ⇒ IntSum = len\n\
     \def three = 1 2 3 >> pack >> Len\nthree >> print",
     ["3"], "")
    -- A TRANSFORMATION OVER A CARRIER THAT HOLDS A FUNCTION (2026-09-14).
    -- The `sample` square is not provable (the two models spell the
    -- same linear map differently) and is decided at the theory's
    -- evidence THROUGH THE EXIT.  Compared as carriers it would be
    -- `eq?` on a quotation, which is syntactic, and this declaration
    -- would be refused for a square that commutes.
  , (closureMod ++ "transformation Scaled : Src ⇒ Dst = toK\n\
     \def run = Scaled >> unK >> (v k -> k 5 >> ev)\n\
     \2 3 >> Two >> run >> print",
     ["15"], "")
    -- the same theory with no `over Doctrine` is not a category: the
    -- spine is left alone, and only the receipt is minted
  , (plainMod ++ "[use Plain ; add1 ; dbl] ; getCode ; unparse ; print",
     ["use@Plain >> add1 >> dbl"], "")
    -- TRANSPORT (5c, reshaped 5c½).  The scope runs: `use Funcs ; add1
    -- ; dbl` is `compose (embed [add1]) (embed [dbl])`, and the EXIT is
    -- called under `over`, which transports nothing.
  , (modeMod ++ "def obs = over Funcs ; chain ; observe\nobs ; print",
     ["16"], "")
    -- what the scope EMITS, read back off the elaborated spine
  , (modeMod ++ "[use Funcs ; add1 ; dbl] ; getCode ; unparse ; print",
     ["use@Funcs >> [add1] >> Funcs@embed >> _ [dbl] >> _ Funcs@embed >> Funcs@compose"], "")
    -- a transporting model declares a WORD of its own name as well, so
    -- the same functor is a value: `[Funcs]` is a quote and the code it
    -- returns splices and runs.  It seeds with an identity carrier
    -- (`leftId` is the law that says the seed is free), which is the one
    -- way it differs from the scope.
  , (modeMod ++ "[add1] ; getCode ; Funcs ; unparse ; print",
     ["[_] >> Funcs@embed >> _ [add1] >> _ Funcs@embed >> Funcs@compose"], "")
    -- and `lift2 [Funcs]` applies it at RUNTIME with the program as its
    -- own witness: transport CHANGES the type, so the witness refuses
    -- the rewrite and the original runs.  That is the fallback working,
    -- not failing.
  , (modeMod ++ "([Funcs] [add1] ; lift2) 5 ; ev ; print", ["6"], "")
    -- STAGE 5c½, THE ROUTING.  A hom-object names ONE wire on each
    -- side, so a wide stage is PACKED with the pairing the strength
    -- names — read off `first`'s declared type, nothing built in — and
    -- a narrow one is whiskered with `first` once per wire above it.
  , (wideMod ++ "def sq = use Wide ; dup ; *\n\
     \def run = over Wide ; sq ; _ 5 ; runW\nrun ; print", ["25"], "")
  , (wideMod ++ "[use Wide ; dup ; *] ; getCode ; unparse ; print",
     ["use@Wide >> [dup >> P] >> Wide@embed >> _ [unP >> *] >> _ Wide@embed \
      \>> Wide@compose"], "")
    -- a three-wire stage, and a stage that acts on a wire that is not
    -- the deepest
  , (wideMod ++ "def poly = use Wide ; dup ; _ dup ; _ _ add1 ; _ * ; +\n\
     \def run = over Wide ; poly ; _ 5 ; runW\nrun ; print", ["35"], "")
    -- `...` is what the strength becomes: `add1 ...` acts on the deepest
    -- wire and the one above it rides along, which is `first`
  , (wideMod ++ "[use Wide ; dup ; add1 ... ; *] ; getCode ; unparse ; print",
     ["use@Wide >> [dup >> P] >> Wide@embed >> _ [add1 pass] >> _ Wide@embed \
      \>> _ Wide@first >> Wide@compose >> _ [unP >> *] >> _ Wide@embed \
      \>> Wide@compose"], "")
  , (wideMod ++ "def w = use Wide ; dup ; add1 ... ; *\n\
     \def run = over Wide ; w ; _ 5 ; runW\nrun ; print", ["30"], "")
    -- LEVEL ONE, composition alone: carriers built by hand compose, and
    -- the composite is a word of the category with no label on it
  , (halfMod ++ "def f = over HW ; [inc] ; H\ndef g = over HW ; [dbl] ; H\n\
     \def fg = over HW ; f g ; compose\nfg ; unH ; _ 5 ; ev ; print", ["12"], "")
    -- OVER/USE COHERENCE: the transport writes out what `over` writes
    -- by hand, so the two denote the same morphism
  , (wideMod ++ "def byHand = over Wide ; [add1] ; embed ; _ [dbl] ; _ embed ; compose\n\
     \def byUse = use Wide ; add1 ; dbl\n\
     \def h5 = over Wide ; byHand ; _ 5 ; runW\n\
     \def u5 = over Wide ; byUse ; _ 5 ; runW\n\
     \h5 u5 ; eq? ; (forget ; \"same\" | forget ; \"differ\") ; merge ; print",
     ["same"], "")
  , (sealedMod ++ "def g2 = use Sealed ; guarded ; inc\n\
     \g2 ; unCap ; _ 5 ; ev ; print", ["8"], "")
    -- A RECEIPT IS `pass` WITH A LABEL, so the normalizer erases it as
    -- it erases `pass`.  Without this no law could be stated about a
    -- program written under any `use` scope: `use@F` has no closed
    -- arity, and `sameCode` refused the whole comparison.
  , (idF ++ "def v = (\"proved\" | \"not proved\") ; merge\n\
     \[use Same ; dup ; _ dup] [dup ; dup _] ; sameCode ; v ; print",
     ["proved"], "")
  ]

-- a rule set over four interchangeable words, reused by the 5b tests
ruleMod :: String
ruleMod =
  "def dupInt = dup >> _ _ 0 >> _ +\ndef twice = dup >> +\ndef double = 2 _ >> *\n\
  \model Opt : Base = dupInt = dup, twice = double\n"

optimizerTheory :: String
optimizerTheory =
  "theory Optimizer\n    ap     : Code ⇒ Code\n    sample : • ⇒ Code\n\
  \    law preservesId = (nil >> ap) nil >> sameCodeC\n\
  \    law idempotent  = (sample >> ap >> ap) (sample >> ap) >> sameCodeC\n"

-- (module source, substring expected in the error)
-- A module that must fail, and whose message must NOT contain the
-- fragment (2026-09-15).  The negatives of the located hints: a
-- heuristic that fires where it has no business is worse than no
-- heuristic, so each one is pinned from both sides.
-- (source, fragment that must be absent)
moduleNoHintTests :: [(String, String)]
moduleNoHintTests =
    -- a one-line source has one line, and naming it says nothing
  [ ("\"x\" 1 ; +", "line ")
    -- a line that SAYS it is unfinished is continued, so the `(` below
    -- it is not a new stage and the rule is not the problem
  , ("def f =\n  1 ;\n  (a b -> a b ; +)\n1 ; f ; print",
     "A new line is a new stage")
    -- a group that IS the last atom of its stage keeps its width
  , ("def f =\n  1 ; (a b -> a b ; +)\n1 ; f ; print",
     "instantiated CLOSED")
    -- no line of this row starts with `|`
  , ("def f =\n  1\n  (a b -> a b ; +)\n1 ; f ; print",
     "A row arm on its own line")
    -- ...and nothing in it is a residual
  , ("def f =\n  1\n  (a b -> a b ; +)\n1 ; f ; print",
     "An open injection leaves a residual")
    -- `use Recursive` is in the header, but the refusal is not an
    -- occurs check and no row is in sight
  , ("def r =\n  use Recursive\n  \"x\" ; +\n1 ; r ; print",
     "wants `merge` after the row")
    -- a row that fails without a knot in it
  , ("def arms = (n ->\n    n 0 ; lt?\n    ((x -> 1)\n    | (x -> 2)) ; merge)\n1 ; arms ; print",
     "wants `merge` after the row")
  ]

moduleFailTests :: [(String, String)]
moduleFailTests =
    -- LOCATIONS (2026-09-15).  Checked without a file, a refusal still
    -- names the line of the text it was handed: the stage that failed
    -- inside a def body, and the stage that failed in a main program.
    -- APPLYING A FAMILY (2026-09-15).  Four ways to get it wrong, each
    -- refused with the spelling that is right: a family is not a model,
    -- a model is not a family, the argument must be a model in scope,
    -- and it must model the theory the parameter declares.
  [ (famSrc ++ "def d = use Fwd ; cube\nd ; drop",
     "`use Fwd`: Fwd is a model PARAMETERIZED by a model")
  , (famSrc ++ "def d = use Floats(Fwd) ; cube\nd ; drop",
     "Floats is not a parameterized model at this point")
  , (famSrc ++ "def d = use Fwd(Nope) ; cube\nd ; drop",
     "`use Fwd(Nope)`: Nope is not a model declared at this point")
  , (famSrc ++ "theory Mon(a) =\n    op : a a \8658 a\n\
      \model Ints : Mon(Int) =\n    op = +\n\
      \def d = use Fwd(Ints) ; cube\nd ; drop",
     "the parameter 'R' of model Fwd takes a model of Ring, and Ints models Mon")
    -- ...and a FALSE family, refused where it is first applied
  , (badFamSrc ++ "def d = use Fwd(Floats) ; cube\nd ; drop",
     "law 'addComm' fails for model Fwd(Floats)")
  , (badFamSrc ++ "def d = use Fwd(Floats) ; cube\nd ; drop",
     "laws are checked AT EACH INSTANTIATION")
  , ("def f =\n    1 2 ; +\n    \"x\" ; +\n1 ; print",
     "line 3, in def f: Cannot unify types: Str vs Int")
  , ("1 ; print\n2 ; print\n\"x\" 1 ; +",
     "line 3: Cannot unify types: Str vs Int")
    -- HINTS (2026-09-15).  Each names the RULE behind the refusal and
    -- what to write instead, and each fires only on a syntactic shape
    -- the checker can see in the source.  Its negative is in
    -- `moduleNoHintTests`.
    -- a new line is a new stage, and a `(` does not continue one
  , ("def f =\n  1\n  (a b -> a b ; +)\n1 ; f ; print",
     "A new line is a new stage, so this `(` does not continue the line \
     \above: end that line with `\\` to carry the stage on, or write `;` \
     \at either end to compose (MANUAL \167\&4).")
    -- a row arm on its own line is a stage, so the arms compose
  , ("def arms = (n ->\n    n 0 ; lt?\n    ((x -> 1)\n    | (x -> 2)) ; merge)\n1 ; arms ; print",
     "A row arm on its own line is a new STAGE, so the arms compose at \
     \`>>` instead of standing side by side")
    -- a grouped atom that is not last in its stage is closed
  , ("def h = 1 2 (a b -> a b ; +) 3 ; drop\n1 ; print",
     "A grouped atom in non-final position is instantiated CLOSED, so \
     \its width is fixed here: pin it with `id`, or move the group last \
     \in its stage (MANUAL \167\&14).")
    -- a recursive call inside a row, with no `merge` to close it
  , ("def lt100? = _ 100 >> lt? >> (_ drop | _ drop)\n\
     \def double = 2 _ >> *\n\
     \def until100 =\n\
     \  use Recursive\n\
     \  lt100?\n\
     \  double >> until100 | _\n\
     \1 >> until100 >> print",
     "A recursive call inside a row usually wants `merge` after the \
     \row: the row leaves the alternatives open, and the knot cannot \
     \close them (MANUAL \167\&14).")
    -- an open injection leaves a residual, and a written type has none
  , ("data Res = (Int | Str)\ndef mk = alt1\ndef use2 = 1 ; mk ; unRes\n1 ; print",
     "An open injection leaves a residual (`\963`), and a written type \
     \has none: close the row with `(pass | pass)` (MANUAL \167\&14).")
    -- the sandbox already named the fix; what it lacked was the line
  , ("data Quiet = (Fn\10216Str \8658 \8226\10217)\n[print] ; Quiet ; drop",
     "line 2: Cannot unify effects")
    -- ATTRIBUTION (2026-09-15).  `in def X` is wrapped ONCE around
    -- everything a def's check can refuse, so the lexer's `\`
    -- continuation, the parser, and the refusals about the def's own
    -- NAME carry it too — and so does the location.
  , ("def f =\n  1 2 \\ x\n  ; +\n1 ; f ; print",
     "line 2, in def f: A `\\` continues a tensor stage onto the next \
     \line, so it must be the last thing on its line")
  , ("def g =\n  1 2\n  ; ; +\n1 ; g ; print",
     "line 2, in def g: Expected a tensor stage")
  , ("def h =\n  1 2\n  ( a -> a\n1 ; h ; print",
     "line 3, in def h: Unclosed group (expected ')')")
  , ("def dup2 = 1\ndef dup2 = 2\n1 ; print",
     "in def dup2: Duplicate definition: dup2")
  , ("def selfie = 1 ... >> + >> selfie\n1",
     "in def selfie: `selfie` refers to itself")
  ] ++
    -- NAMED FIELDS refuse five things by name (2026-09-14).  A field
    -- name is a WORD, so it collides like one; fields name the
    -- positions of ONE constructor; and a named position is one wire.
  [ ("data Bad = (a: Int | b: Str)\n1 ; print",
     "field names name the positions of ONE constructor")
  , ("data T1 = (px: Int)\ndata T2 = (px: Str)\n1 ; print",
     "field name 'px' is already a word in scope")
  , ("data T3 = (len: Int, b: Str)\n1 ; print",
     "field name 'len' is already a word in scope")
  , ("type T5 = (a: Int, b: Str)\n1 ; print",
     "field names are for `data` declarations")
  , ("data T6 = (a: Int, a: Str)\n1 ; print",
     "duplicate field name 'a'")
  , ("data W = (x: Int Str, y: Int)\n1 ; print",
     "2 field names for 3 field positions")
  , ("data W2 = (2x: Int, y: Str)\n1 ; print",
     "'2x' is not a word, so it cannot name a field")
    -- ONE COMPONENT PER PARAMETER (2026-09-14): a natural
    -- transformation between models of a two-parameter theory is two
    -- components, and one is refused by name.
  , ("data Dual = Float Float\n\
     \def zt = (d -> 0.0)\n\
     \def dadd = Dual(a, da) Dual(b, db) -> (a b ; fadd) (da db ; fadd) ; Dual\n\
     \def val = Dual(v, t) -> v\n\
     \def tan = Dual(v, t) -> t\n\
     \theory S(a, g) =\n\
     \    lit : Float \8658 a\n\
     \    add : a a \8658 a\n\
     \    sample : \8226 \8658 a\n\
     \    observe : a \8658 Float\n\
     \    grad : a \8658 g\n\
     \model F : S(Float, Float) =\n\
     \    lit = id\n\
     \    add = fadd\n\
     \    sample = 1.5\n\
     \    observe = id\n\
     \    grad = zt\n\
     \model D : S(Dual, Float) =\n\
     \    lit = (c -> c 0.0 ; Dual)\n\
     \    add = dadd\n\
     \    sample = 1.5 1.0 ; Dual\n\
     \    observe = val\n\
     \    grad = tan\n\
     \transformation V : D \8658 F = val\n\
     \1 ; print",
     "a natural transformation has ONE COMPONENT PER PARAMETER")
    -- A BINDER PATTERN refuses two things by name (2026-09-14): a
    -- multi-alternative carrier (it un-constructs ONE alternative) and
    -- an arity that is not the constructor's.
  , ("data Shape = (Int | Int Int)\ndef f = Shape(a) -> a\n1 ; print",
     "`Shape` has 2 alternatives and a pattern un-constructs ONE")
  , ("data Dual = Float Float\ndef f = Dual(a, b, c) -> a\n1 ; print",
     "names 3 fields, but `Dual` has 2")
    -- HYGIENE: abstraction elimination EMITS `capture` and `dist2` into
    -- reflected code, so a module def of either name would capture code
    -- that never mentioned it.  They are the two prelude names a module
    -- may not shadow (stage 5a¾).
    -- `fdiv` keeps `div`'s one refusal: dividing by zero has no answer
    -- worth inventing.  Everything else that leaves the finite doubles
    -- is IEEE and prints as itself.
  , ("1.0 0.0 ; fdiv ; print", "division by zero")
  , ("def capture = dup\n1 >> print",
     "`capture` cannot be shadowed: abstraction elimination EMITS it")
  , ("def dist2 = dup\n1 >> print",
     "`dist2` cannot be shadowed: abstraction elimination EMITS it")
    -- a FALSE law rejects the module when it starts running
  , ("theory M(a) =\n    unit : • ⇒ a\n    op : a a ⇒ a\n    sample : • ⇒ a\n    law leftUnit = (sample ; unit ... ; op) sample ; eq? ; (forget ; true | forget ; false) ; merge\nmodel BadUnit : M(Int) =\n    unit = 1\n    op = +\n    sample = 7\n1 >> print",
     "law 'leftUnit' fails for model BadUnit")
    -- the evalCode arity gap: spliced code produces 2 wires but the
    -- context typed the hit track as 0 (Δ is existential, chosen by the
    -- caller). Used to leak silently (a value on a stack typed empty);
    -- the top-level width backstop now catches it as a clean error,
    -- delivering the guarantee spec-code.md already claimed.
    -- box's first operand is the WITNESS, so handing it only the code
    -- is an ordinary arity/type error rather than anything exotic
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\n(2 ([1 2 >> + >> dup >> *] >> getCode) >> take) >> box\nev >> (print | forget) >> merge",
     "Cannot unify types")
    -- a model body must SUBSUME its slot's declared type, effect row
    -- included: an io body under a pure-declared slot used to pass the
    -- stack-only check, and `functor F = <that slot>` then carried IO
    -- into elaboration, breaking the phase invariant.
  , ("theory Rewriter =\n    rw : Code ⇒ Code\n\nmodel Loud : Rewriter =\n    rw = _ \"x\" ; _ print\n\ndef loud = use Loud ; rw\n1",
     "Cannot unify effects: IO vs pure")
    -- a witness is not optional: `evalAs` without one is an arity error
    -- (there is no longer any way to splice without stating the type)
  , ("def bad = (cd x -> (cd) ... >> evalAs >> ((y -> y x >> pack) | forget >> nil) >> merge)\n1",
     "Cannot unify")
    -- (was a "result desync" moduleFailTest: spliced code produced 2
    -- wires where the context typed the hit track as 1.  The splice
    -- check now catches that AT the splice, so it rides the miss track
    -- instead of reaching the top-level width backstop — see evalTests.)
    -- the case(…) special form is gone: `case` is an ordinary unknown name
  , ("1 >> alt1 >> case(drop, drop)\n1", "Unclosed group")
    -- composition is exact: a word threading a resource the scope does
    -- not have (or in another order) is still a routing error, with the
    -- mismatch named on both sides
  , ("resource Log = Str\nresource Counter = Int\ndef bump = unCounter >> 1 ... >> + >> Counter\ndef note = unLog _ >> cat >> Log\ndef step = use Log Counter >> toStr >> note >> bump\ndef bad = use Counter Log >> step\n1",
     "threads Log Counter, but this scope is over Counter Log")
    -- a functor's word must be a pure `Code ⇒ Code`, checked at the
    -- first use (declarations are hoisted, so that is where the prefix
    -- scope is what it will be at run time)
  , ("def w = dup >> *\nfunctor F = w\ndef p = use F ; 1 ... >> +\n3 >> p >> print",
     "must be Code ⇒ Code")
  , ("def w = (c -> c >> unparse >> print >> c)\nfunctor F = w\ndef p = use F ; 1 ... >> +\n3 >> p >> print",
     "must be pure")
  , ("functor F = nosuch\ndef p = use F ; 1 ... >> +\n3 >> p >> print",
     "not defined at this point")
    -- purity is not totality: the budget is what stands between a
    -- looping functor and a hung compiler
  , ("def w = [(self c -> c >> self ... >> ev)] ... >> fix ... >> ev\nfunctor F = w\ndef p = use F ; 1 ... >> +\n3 >> p >> print",
     "step budget exhausted")
  , ("def idF = (c -> c)\nfunctor F = idF\nfunctor F = idF\n1",
     "Duplicate functor declaration")
    -- STAGE 4½: a label is minted by a scope or not at all.  The
    -- receipt is a word in the environment (it has to be — it is the
    -- arrow that carries the label), so the source is checked for it.
  , (idF ++ "def forged = use@Same >> dup >> *\n5 >> forged >> print",
     "not a word: a label is minted by a scope, never written by hand")
    -- STAGE 4¾: an import names a FILE, and a file read is the loader's
    -- IO — so a module checked from a string has nothing to resolve it
    -- against, and says so rather than ignoring the line
  , ("import \"util.braid\"\ndef f = dup >> +\n2 >> f >> print",
     "a module can only import when it is loaded from a file")
    -- `interpose` (stage 4) admits only unit endomorphisms — `ρ ⇒ ρ`,
    -- or `E ρ ⇒ E ρ` over resource wires — and refuses by name, with
    -- the stage's actual type, before inserting it anywhere.  Checked
    -- by SUBSUMPTION: `Int ρ ⇒ Int ρ` is a model of `ρ ⇒ ρ` but
    -- not as general as it, and fails at any empty cut.
  , ("def peek = [dup ... >> print ...] >> getCode\ndef peeked = peek ... >> interpose\nfunctor Peeked = peeked\ndef bad = use Peeked >> dup >> +\n3 >> bad >> print",
     "interpose: `dup pass >> print pass` is a0 ρ0 =IO> a0 ρ0, which reads a wire")
  , ("def inc = [1 ... >> + ...] >> getCode\ndef inced = inc ... >> interpose\nfunctor Inced = inced\ndef bad = use Inced >> dup >> +\n3 >> bad >> print",
     "is Int ρ0 ⇒ Int ρ0, which reads a wire")
  , ("def w = [0 ...] >> getCode\ndef wd = w ... >> interpose\nfunctor W = wd\ndef bad = use W >> dup >> +\n3 >> bad >> print",
     "`0 pass` is ρ0 ⇒ Int ρ0, not an endomorphism")
    -- a resource stage passes the check, and then the scope must
    -- actually thread the resource: this is the re-inference of the
    -- expansion, and the error is an ordinary one
  , ("resource Fuel = Int\ndef burn = unFuel >> _ 1 >> - >> Fuel\ndef metered = ([burn ...] >> getCode) ... >> interpose\nfunctor Metered = metered\ndef bad = use Metered >> dup >> +\n3 >> bad >> print",
     "Cannot unify types: Int vs Fuel")
    -- outside the fragment `sameCode` REPORTS, rather than guessing:
    -- "I cannot tell" is not "they differ".  Since 2026-09-13 the
    -- boundary is narrower and each refusal names what stopped it.
    -- `ev` of a WIRE whose arrow is OPEN: `ev`'s own scheme takes the
    -- whole remaining segment, so there is no arity to give it.  Since
    -- 2026-09-13 that is the only `ev` left outside — one whose arrow
    -- is closed is a neutral application, decided like any other word.
  , ("[ev] [ev] ; sameCode ; drop ; 1",
     "outside the structural fragment: `ev` of a value whose arrow is \
     \not closed")
    -- `loop` is `fix`, and a fixpoint equation is an axiom of an
    -- iteration theory, not an equation of the free category
  , ("[loop] [loop] ; sameCode ; drop ; 1",
     "outside the structural fragment: `loop` has no closed arity")
    -- a sum whose injection is unknown AND whose row is a bare tail:
    -- unnamed tracks have no widths, so there is no partition to split
  , ("[merge] [merge] ; sameCode ; drop ; 1",
     "outside the structural fragment: a sum whose injection is unknown \
     \and whose row has no closed tracks")
    -- THE TERMINATION GUARD.  Each `st` splits the case tree in two, so
    -- seventeen of them would be 2^17 leaves; the normalizer stops at
    -- sixteen splits and says so.  Running out of room is reported as
    -- OUTSIDE the fragment, never as a verdict.
  , ("def st = dup >> eq? >> (_ drop | _ drop) >> merge\n\
     \[st >> st >> st >> st >> st >> st >> st >> st >> st >> st >> st \
     \>> st >> st >> st >> st >> st >> st] [id] >> sameCode >> drop >> 1",
     "outside the structural fragment: the case tree grew past 16 splits")
  , ("def square = dup >> *\ndef square = id\n1", "Duplicate definition")
  , ("def while = drop\ndef while = id\n1",       "Duplicate definition")
  , ("type Bool = (• | •)\ntype Bool = (• | •)\n1", "Duplicate type declaration")
  , ("type Foo = (• | Unknowable)\n1",           "Unknown type name")
    -- width parameters: declared by USE (a parameter under `^`), so a
    -- bare ^n with no such parameter is the error now
  , ("type Bad = (• | Int^n)\n1",                  "not a parameter of this declaration")
  , ("type Bad(n) = (Int^n n)\n1",                 "both as a wire and as a width")
  , ("data BadD(n) = (• | Int^n)\n1",              "`type` aliases only")
  , ("type Bad = (• | Int^)\n1",                 "Expected an exponent")
  , ("type = (• | •)\n1",                        "Malformed type declaration")
  , ("type Pair(a, b) = (a | Int)\n1",           "must occur in the body")
  , ("data Bad(...) = (... Int)\n1", "must be the last thing in its stack")
  , ("data Bad2(..., a) = (a)\n1",   "must be the last type parameter")
    -- `---` is the ROW tail and obeys the same placement rule as `...`
  , ("data Bad(---, a) = (a | ---)\n1", "'---' must be the last type parameter")
  , ("data Bad2(a) = (a | ---)\n1",     "'---' needs a `---` parameter on the declaration")
  , ("type Bad3(---) = (--- Int)\n1",   "'---' must be the last alternative of its row")
  , ("data Bad4(---) = (Int)\n1",       "every parameter must occur in the body")
  , ("data Bad5(---) = (--- | Int)\n1", "'---' must be the last alternative of its row")
    -- and in a TERM it is the residual, so the old `| ...` spelling is
    -- refused at module level too
  , ("def f = (dup | ...)\n1", "write `| ---` for more alternatives")
    -- a wire parameter given a stack: the mistake this change makes
    -- impossible, reported where you wrote it
  , ("type L = List(Int Str)\n1",    "takes one wire")
    -- rotLast is gone: the splice it was typed with is unspellable
  , ("1 >> rotLast",                  "Unknown primitive: rotLast")
    -- Fin is a built-in type former, not a user name
  , ("type Fin = Int\n1",             "Malformed type declaration")
    -- a resource is unrolled, not eliminated by points: no fold
  , ("resource Log = Str\nfoldLog",   "Unknown primitive: foldLog")
    -- a model is AUDITED: its slots must match the theory's
    -- signatures, read at the model's own argument
  , ("theory Monoid(a) =\n    unit : • ⇒ a\n    op   : a a ⇒ a\nmodel Bad : Monoid(Int) =\n    unit = \"oops\"\n    op   = +\n1",
     "slot 'unit' is • ⇒ Str but theory Monoid declares • ⇒ Int")
    -- STAGE 5a, item 0: a slot-local variable is UNIVERSALLY quantified,
    -- so a model body that is too specific for it is refused, and
    -- the refusal names the slot
  , ("theory Wrap(a) =\n    box : b ⇒ a\nmodel W : Wrap(Str) =\n    box = _ 1 ; + ; toStr\n1",
     "slot 'box' is Int ⇒ Str but theory Wrap declares a0 ⇒ Str")
  , ("theory Wrap(a) =\n    box : b ⇒ a\nmodel W : Wrap(Str) =\n    box = _ 1 ; + ; toStr\n1",
     "must stay parametric in it")
    -- STAGE 5a, item 1: the four ways a constructor parameter goes wrong
  , ("theory Arrow(k(_, _)) =\n    compose : k ⇒ k\n1",
     "Type parameter k is a type constructor of arity 2: it is not a wire, write it applied — k(_, _)")
  , ("theory Arrow(k(_, _)) =\n    compose : k(a) ⇒ k(a)\n1",
     "Type constructor parameter 'k' takes 2 argument(s), but was given 1")
  , ("theory Arrow(k(_, _)) =\n    compose : k(a, b) ⇒ k(a, b)\nmodel Bad : Arrow(Nope) =\n    compose = _\n1",
     "declares 'k' as a type constructor of arity 2, so its argument names a declared data type; 'Nope' is not one")
  , ("data One(a) = a\ntheory Arrow(k(_, _)) =\n    compose : k(a, b) ⇒ k(a, b)\nmodel Bad : Arrow(One) =\n    compose = _\n1",
     "declares 'k' with arity 2, but One takes 1 argument(s)")
    -- `Fn` is built in and takes an arrow, not wires: the refusal says
    -- so, and names the one-line wrapper that works
  , ("theory Arrow(k(_, _)) =\n    compose : k(a, b) ⇒ k(a, b)\nmodel F : Arrow(Fn) =\n    compose = _\n1",
     "`Fn` is built in and takes an arrow, not wires")
    -- a constructor argument is a NAME, not a type expression
  , ("theory Arrow(k(_, _)) =\n    compose : k(a, b) ⇒ k(a, b)\nmodel Bad : Arrow(List(Int)) =\n    compose = _\n1",
     "must be a bare constructor name")
    -- and every parameter of the named constructor must be a wire, or
    -- the substitution would not be sound
  , ("data T(a, ...) = a (...)\ntheory Arrow(k(_, _)) =\n    compose : k(a, b) ⇒ k(a, b)\nmodel Bad : Arrow(T) =\n    compose = _\n1",
     "every parameter of a constructor argument must be a wire")
  , ("theory Monoid(a) =\n    unit : • ⇒ a\n    op   : a a ⇒ a\nmodel Partial : Monoid(Int) =\n    unit = 0\n1",
     "no binding for 'op'")
  , ("theory Monoid(a) =\n    unit : • ⇒ a\n    op   : a a ⇒ a\nmodel Extra : Monoid(Int) =\n    unit = 0\n    op   = +\n    huh  = 1\n1",
     "'huh' is not an operation of theory Monoid")
  , ("theory Monoid(a) =\n    unit : • ⇒ a\n    op   : a a ⇒ a\nmodel I : NoSuch(Int) =\n    unit = 0\n    op = +\n1",
     "Unknown theory: NoSuch")
    -- a law must be a program that can run on nothing and answer yes
  , ("theory T(a) =\n    f : a ⇒ a\n    law silly = 5\nmodel I : T(Int) =\n    f = id\n1",
     "must be a program with type `• ⇒ Bool`")
    -- one resource operation per stage; the elaborator says so
  , ("resource Log = Str\nresource Counter = Int\ndef bump = unCounter >> 1 ... >> + >> Counter\ndef note = unLog _ >> cat >> Log\ndef f = use Log Counter >> \"x\" >> note bump\n1",
     "at most one resource operation")
  , ("resource Log = Str\ndef f = use Log\n1", "ends its scope")
  , ("resource resource = Int\n1",    "Malformed type declaration")
    -- a declared pure Fn type refuses an io quotation: the declaration
    -- is not decoration
  , ("data Quiet = (Fn⟨Str ⇒ •⟩)\n[print] >> Quiet >> drop",
     "Cannot unify effects")
    -- STAGE 5a½: …and it refuses a RECURSIVE one for the same reason.
    -- A codata thunk built by `fix` must be declared `=Recursive>`; the
    -- message says which label to write.
  , ("data Stream(a) = (a Fn⟨• ⇒ Stream(a)⟩)\ndef from = [(self n -> n [n 1 >> + >> self ... >> ev] >> Stream)] ... >> fix ... >> ev\n0 >> from >> drop",
     "Cannot unify effects: Recursive vs pure (composition joins grades, and this arrow's manifest is written and fixed: write =Recursive> on that arrow, or keep this code label-free)")
    -- a NESTED written Fn keeps its grade through the `k := <data>`
    -- substitution: substituting theory parameters used to rebuild every
    -- nested Fn pure, which silently dropped the declared manifest
  , ("theory Emb(k(_, _)) =\n    embed : Fn⟨a =Recursive> b⟩ ⇒ k(a, b)\n\ndata Arr(a, b) = Fn⟨a ⇒ b⟩\n\nmodel A : Emb(Arr) =\n    embed = Arr\n\ndef go = use A ; embed\n[dup >> *] >> go >> drop",
     "slot 'embed' is Fn⟨a0 ⇒ a1⟩ ⇒ Arr(a0, a1) but theory Emb declares Fn⟨a0 =Recursive> a1⟩ ⇒ Arr(a0, a1)")
    -- a theory slot declared pure refuses a `fix`-built body — the same
    -- rule that already refused an io body under a pure slot
  , ("theory Stepper =\n    step : Int ⇒ Int\n\nmodel Fixed : Stepper =\n    step = [(self n -> n >> zero? >> ((z -> 0) | (m -> m 1 >> - >> self ... >> ev)) >> merge)] ... >> fix ... >> ev\n\ndef go = use Fixed ; step\n5 >> go >> drop",
     "slot 'step' is Int =Recursive> Int but theory Stepper declares Int ⇒ Int (Cannot unify effects: Recursive vs pure")
    -- the bound must agree with the bundle's actual width
  , ("fin0 >> 1 2 >> at",             "Cannot unify")
    -- a closed non-final open word that doesn't cover its wires is an
    -- ORDINARY width error now, not a placement violation
  , ("1 2 >> sumN _",  "Cannot unify stacks")
    -- Fn type declarations: missing arrow, unclosed, reserved name
  , ("type Bad(a) = Fn⟨a a⟩\n1",                 "Expected '⇒'")
  , ("type Bad(a) = Fn⟨a ⇒ a\n1",                "close the Fn type")
  , ("type Fn(a) = (• | a)\n1",                  "Malformed type declaration")
  , ("type Bad = Fn\n1",                         "Fn must be written")
    -- STAGE 5a½: a definition is not in scope in its own body, under
    -- either spelling — unless its header SAYS so (5e).
  , ("def f = 1 ... >> + >> f\n1",
     "`f` refers to itself")
  , ("def f = 1 ... >> + >> recurse\n1",
     "`f` refers to itself (`recurse` named the definition being written)")
    -- and the refusal names the way out: the marker, by name
  , ("def f = 1 ... >> + >> f\n1",
     "write `use Recursive` in its header (MANUAL §8)")
    -- STAGE 5e: the marker is a def's HEADER.  The name it puts back in
    -- scope is the DEF's, so a scope opened part-way down the body
    -- would quietly name only that part — refused where it is written.
  , ("def f = 1 ... >> + >> (use Recursive ; drop)\n1",
     "is a def's header")
  , ("use Recursive ; 1", "there is no def here")
    -- and the receipt is still unwritable by hand
  , ("def f = use@Recursive ; 1\n1", "is the receipt of `use Recursive`")
    -- one spelling per thing: the marker owns the name, so a functor
    -- (or model, or theory) of that name is a collision, not a shadow
  , ("def idF = (c -> c)\nfunctor Recursive = idF\ndef f = use Recursive ; (n -> n)\n1",
     "is the built-in recursion marker")
    -- a non-final open-arity atom must report the placement rule, not
    -- panic in appendStack (regression: was a Haskell error).  Until
    -- 5a½ the shortest way to write one was a non-final recursive call
    -- (`def x = x x ... >> +`); an open binder is the shortest now.
  , ("1 2 3 >> (x ... -> x x ... >> + >> +) 4",   "final atom of its tensor stage")
    -- nominal rigidity: a data type is NOT its unfolding
  , ("type Nat = (• | Nat)\nalt1 >> Nat >> unNat >> unNat", "Cannot unify types")
  , ("type dup = (• | dup)\n1",                  "collides")
    -- list elements must be pure pushes (desugar makes it a unify error)
  , ("list(1, 2) >> len >> print",                  "Unclosed group")
  , ("def 5 = id\n1",                             "Malformed definition")
  , ("+",                                         "main requires a nonempty input stack")

    -- TEMPLATES: a template called outside every model scope of its
    -- theory names the THEORY, not a missing word
  , (tmplMod ++ "1 2 ; fold1 ; print",
     "fold1 needs a model of Monoid in scope")
    -- a model of the WRONG theory in scope is the same error:
    -- selection is by theory and nothing is searched for
  , (tmplMod ++ "theory Pointed(a) =\n    pt : • ⇒ a\n\
     \model IntPt : Pointed(Int) =\n    pt = 9\n\
     \def bad = use IntPt ; fold1\n1 2 ; bad ; print",
     "fold1 needs a model of Monoid in scope")
    -- `over` declares what the def IS, so it may only be its own header
  , (tmplMod ++ "def f =\n    1\n    over Monoid\n    op\n1 ; f ; print",
     "`over Monoid` may only be a def's own header")
    -- and `use` no longer takes a theory at all: it applies a functor,
    -- and a theory is not one
  , (tmplMod ++ "def f = use Monoid ; op\n1 ; print",
     "`use Monoid` names a theory: `use` applies a functor, and a theory \
     \is not one — write `over Monoid` to make this def a template")
    -- one model is waited for, so exactly one name is `over`ed
  , (tmplMod ++ "theory Pointed(a) =\n    pt : • ⇒ a\n\
     \def f = over Monoid Pointed ; op\n1 ; print",
     "an `over` header names exactly one theory")
    -- expansion is inlining, so a template cannot recurse
  , (tmplMod ++ "def loopy = over Monoid ; dup ; op ; loopy\n\
     \def go = use IntSum ; loopy\n1 ; go ; print",
     "template loopy calls itself")
    -- `@` IS THE COMPILER'S (stage 5a item 2a).  A slot's generated
    -- name is refused in source exactly as a functor's receipt is, and
    -- the message names the scope that reaches it.
  , (tmplMod ++ "def q = IntSum@op\n1 2 ; q ; print",
     "`IntSum@op` is the compiler's spelling of a slot: reach it with \
     \`use IntSum`")
  , (tmplMod ++ "1 2 ; IntSum@op ; print",
     "is the compiler's spelling of a slot")
    -- a template shares the def namespace
  , (tmplMod ++ "def fold1 = dup\n1 ; print", "Duplicate definition: fold1")
    -- STAGE 5b/5c½: MODELS OF `Base`.  `q` may stand wherever `p`
    -- stands iff scheme(q) >= arrow(p).  That is rank-2, so no `Fn` type
    -- holds it and no call site checks it: it is checked ONCE, here, by
    -- the routine `checkInstance` and `runAs` already share.
  , ("def dupInt = dup >> _ _ 0 >> _ +\nmodel Bad : Base = dup = dupInt\n1 >> print",
     "model Bad : Base: `dup = dupInt` is refused: dup is used at a0 \8658 a0 a0 but dupInt is Int \8658 Int Int")
  , ("def dupInt = dup >> _ _ 0 >> _ +\nmodel Bad : Base = dup = dupInt\n1 >> print",
     "A binding may only GENERALIZE")
    -- the parametricity case: `two = dup` would RUN on an Int and
    -- narrows `a ⇒ Int Int` to `Int ⇒ Int Int` everywhere else
  , ("def two = drop 1 1\nmodel Bad : Base = two = dup\n1 >> print",
     "model Bad : Base: `two = dup` is refused: two is used at a0 \8658 Int Int but dup is a0 \8658 a0 a0")
  , ("def two = drop 1 1\nmodel Bad : Base = two = dup\n1 >> print",
     "must stay parametric in it")
    -- GRADES ride along by the semilattice order: an io image under a
    -- pure generator is refused (the other direction passes)
  , ("def noisy = toStr >> print\ndef quiet = drop\nmodel Bad : Base = quiet = noisy\n1 >> print",
     "model Bad : Base: `quiet = noisy` is refused: quiet is used at a0 \8658 \8226 but noisy is a0 =IO> \8226")
  , ("def noisy = toStr >> print\ndef quiet = drop\nmodel Bad : Base = quiet = noisy\n1 >> print",
     "the expected type fixes the grade; this code must stay pure")
    -- a slot is not a word outside `use`, so it is neither side of a
    -- binding; nor is a theory, nor a template (which has no type until
    -- a model supplies one)
  , ("theory Mon(a) =\n    op : a a \8658 a\nmodel Plus : Mon(Int) =\n    op = +\n\
     \model Bad : Base = op = +\n1 >> print",
     "op is a slot of theory Mon, and a slot is not a word outside `use`")
  , ("theory Mon(a) =\n    op : a a \8658 a\nmodel Plus : Mon(Int) =\n    op = +\n\
     \model Bad : Base = Plus@op = +\n1 >> print",
     "is the compiler's spelling of a slot")
  , ("theory Mon(a) =\n    op : a a \8658 a\nmodel Plus : Mon(Int) =\n    op = +\n\
     \model Bad : Base = Mon = +\n1 >> print",
     "model Bad : Base: Mon is a theory, not a word")
  , ("theory Mon(a) =\n    op : a a \8658 a\nmodel Plus : Mon(Int) =\n    op = +\n\
     \def twice = over Mon ; op\nmodel Bad : Base = twice = +\n1 >> print",
     "twice is a template over theory Mon")
  , ("model Bad : Base = nowhere = dup\n1 >> print",
     "model Bad : Base: nowhere is not defined at this point")
    -- the shape of a binding: v1 sends one WORD to one word
  , ("model Bad : Base = dup dup = dup\n1 >> print",
     "a v1 binding sends one WORD to one word")
  , ("model Bad : Base = dup\n1 >> print",
     "is missing `=` (a binding reads `p = q`)")
  , ("model Bad : Base\n1 >> print", "model Bad : Base: no bindings")
  , ("model Bad : Base = dup = swap, dup = drop\n1 >> print",
     "two bindings give `dup` an image")
    -- STAGE 5c½: `over` names a theory or a model with a carrier, and
    -- nothing else.  Each other kind is refused by kind, with the word
    -- to write.
  , (modeMod ++ "def idF = (c -> c)\nfunctor Same = idF\n\
     \def bad = over Same ; add1\n1 ; print",
     "`over Same` names a functor, and a functor is applied to a body, \
     \not inhabited by one.  Write `use Same`.")
  , (modeMod ++ "resource Log = Str\ndef bad = over Log ; add1\n1 ; print",
     "`over Log` names a resource, and a resource is threaded through a \
     \body.  Write `use Log`.")
  , (modeMod ++ "def bad = over Nope ; add1\n1 ; print",
     "`over Nope` names nothing declared at this point")
  , ("def dupInt = dup\nmodel Opt : Base = dupInt = dup\n\
     \def bad = over Opt ; dupInt\n1 ; print",
     "`over Opt` names a model of Base — a rewriting of the ambient \
     \presentation, which is applied, not inhabited.  Write `use Opt`.")
    -- `over` of a model with NO carrier: there is nothing to build
  , ("theory Ring(a) =\n    add : a a ⇒ a\nmodel Ints : Ring(Int) =\n\
     \    add = +\ndef bad = over Ints ; 1\n1 ; print",
     "`over Ints` names a model of Ring in the base: it has no carrier \
     \to build — write `use Ints`, or `over Ring` for a template.")
    -- the K-word ascription is a WRITTEN expectation, checked against
    -- the arrow: one carrier out of nothing, or it is refused
  , (modeMod ++ "def bad = over Funcs ; add1\n1 ; print",
     "`over Funcs`: bad neither builds one of Funcs's carriers — \
     \`• ⇒ Arr(a, b)`, which is what a morphism of the category is — \
     \nor uses any of Funcs's words, so the header did nothing: bad is \
     \Int ⇒ Int")
  , (modeMod ++ "def bad = over Funcs ; 5\n1 ; print",
     "drop the header and let `use Funcs` transport the def.")
    -- the keywords that are gone, and where they went
  , ("rules Bad = dup => dup\n1 >> print",
     "`rules` is gone: a rule set is a PARTIAL MODEL of the ambient \
     \presentation, so it is written `model Name : Base = p = q")
  , ("instance Bad : Base = dup = dup\n1 >> print",
     "`instance` is spelled `model` since 2026-09-13: write \
     \`model Bad : Base = dup = dup`.  MANUAL §8.")
  , (modeMod ++ "mode K = Funcs\n1 ; print",
     "`mode` is gone: a model whose theory has a hom-object `k(_, _)` \
     \transports when it is USED, so the model IS the declaration — \
     \write `use Funcs` where you wrote `use K`")
  , (monoidMod ++ "morphism Len : ListMonoid ⇒ IntSum = len\n1 >> print",
     "`morphism` is spelled `transformation` since 2026-09-14: a map \
     \between two models of a theory is a NATURAL TRANSFORMATION between \
     \the functors they are — write `transformation Len : ListMonoid ⇒ \
     \IntSum = len`.  MANUAL §8.")
    -- `Base` is the ambient presentation and is not written down
  , ("theory Base =\n    op : a \8658 a\n1 >> print",
     "`Base` is the ambient presentation and may not be declared")
    -- a model of `Base` shares one namespace with functors
  , ("def idF = (c -> c)\nfunctor Opt = idF\nmodel Opt : Base = dup = dup\n1 >> print",
     "Duplicate model declaration: Opt")
    -- `sameCodeC` reports outside the fragment exactly as `sameCode`
    -- does — they are one procedure — and a `fix` body that applies its
    -- self wire is where the boundary now falls
  , ("def dupSwap = dup >> swap\nmodel Opt : Base = dupSwap = dup\n\
     \def slow = [[self ... -> _ 100 >> lt? >> (_ drop | _ drop) \
     \>> (dupSwap >> + >> self ... >> ev | _) >> merge] ... >> fix ... >> ev]\n\
     \(slow >> getCode >> Opt) (slow >> getCode) >> sameCodeC >> drop >> 1 >> print",
     "sameCodeC: outside the structural fragment: `ev` of a value whose \
     \arrow is not closed")
    -- the audit: a model that fails a law is not a model.
    -- `doubled` repeats every stage, so weaving twice weaves twice.
  , ("def doubled = [(s -> (s >> pack) (s >> pack) >> append)] ... >> stagewise\n\
     \theory Optimizer\n    ap     : Code \8658 Code\n    sample : \8226 \8658 Code\n\
     \    law idempotent = (sample >> ap >> ap) (sample >> ap) >> sameCodeC\n\
     \model Dbl : Optimizer\n    ap     = doubled\n    sample = [dup >> swap] >> getCode\n1 >> print",
     "law 'idempotent' fails for model Dbl")
    -- EXITS ARE THE ONLY WAY OUT, and they are out: a slot that takes
    -- the carrier and returns base is refused inside the transporting
    -- scope.  That is what makes the K-word table exact without
    -- inference — every word written under `use M` produces a carrier.
  , (modeMod ++ "def bad = use Funcs ; add1 ; observe\nbad ; drop",
     "`observe` leaves Funcs; call it outside `use Funcs`")
    -- THE LEVELS, each pinned.  Composition alone: `over M ; f g ;
    -- <compose>` is fine (see evalTests), but there is no embedding, so
    -- `use M` has nothing to transport a base stage WITH.
  , (halfMod ++ "def bad = use HW ; inc ; inc\nbad ; drop",
     "`use HW`: theory Half takes Doctrine's `compose` and not its \
     \`embed` (`Fn⟨a ⇒ b⟩ ⇒ k(a, b)`): `use HW` cannot transport a base \
     \stage; `over HW` and compose by hand.")
    -- + embedding: single-wire stages transport, and a WIDER stage is
    -- refused naming the strength that would carry it
  , (modeMod ++ "def bad = use Funcs ; dup ; *\nbad ; drop",
     "`use Funcs`: dup is not one wire in and one wire out, and theory \
     \Arrow's hom-object Arr(a, b) names ONE object on each side.  A wider \
     \stage transports through `first` — Doctrine's strength, `k(a, b) \8658 \
     \k(p(a, c), p(b, c))`, whose pairing the elaborator packs with — and \
     \theory Arrow does not declare it.")
    -- and a stage that does not cover the stack it is handed
  , (wideMod ++ "def bad = use Wide ; dup ; add1 ; *\nbad ; drop",
     "`use Wide`: add1 takes 1 wire, but the scope is running 2 wires \
     \wide.")
    -- a stage that takes no wire has no object to be the source of
  , (wideMod ++ "def bad = use Wide ; 5 ; dbl\nbad ; drop",
     "`use Wide`: 5 takes no wire, and W(a, b) has an object on each side")
    -- THE CLAIM IS CHECKED.  `over Doctrine` says a slot of that name
    -- IS the doctrine's, so a slot of that name at another signature is
    -- refused, naming both arrows.  (This replaces the "two slots at
    -- one shape" refusal: names are read now, so two slots cannot
    -- collide at one meaning.)
  , ("data W(a, b) = Fn⟨a ⇒ b⟩\n\
     \theory Bent(k(_, _)) over Doctrine =\n\
     \    compose : k(a, b) k(b, c) ⇒ k(a, b)\n\
     \def thenW = (f g -> [(x -> f ; unW ; _ x ; ev ; (y -> g ; unW ; _ y ; ev))] ; W)\n\
     \model TW : Bent(W) =\n    compose = (f g -> f g ; drop)\n1 ; print",
     "theory Bent: slot 'compose' is k(a0, a1) k(a1, a2) ⇒ k(a0, a1), but \
     \Doctrine declares it k(a0, a1) k(a1, a2) ⇒ k(a0, a2)")
    -- and `over Doctrine` that takes none of its operations did nothing
  , ("data W(a, b) = Fn⟨a ⇒ b⟩\n\
     \theory Bare(k(_, _)) over Doctrine =\n\
     \    only : k(a, b) ⇒ k(a, b)\n\
     \model TW : Bare(W) =\n    only = _\n1 ; print",
     "`over Doctrine` declares nothing")
    -- TRANSFORMATIONS (5d).  A square that does not commute is named, and the
    -- verdict comes from the samples because `len` is opaque to the
    -- normalizer: `lenUp` adds one, so the unit square breaks first.
  , (monoidMod ++ "def lenUp = (l -> l >> len >> _ 1 >> +)\n\
     \transformation Bad : ListMonoid ⇒ IntSum = lenUp\n1 >> print",
     "transformation Bad: the square for slot 'unit' does not commute at \
     \the \
     \theory's samples")
    -- ...and a component that is wrong in the VALUE is caught through
    -- the exit, on a carrier `eq?` could only have weighed by spelling
  , (closureMod ++ "def toKBad = unTwo >> (v f -> (v 1 >> +) \
     \[(d -> d f >> *)] >> K)\n\
     \transformation Scaled : Src ⇒ Dst = toKBad\n1 >> print",
     "transformation Scaled: the square for slot 'sample' does not commute \
     \at \
     \the theory's samples")
    -- ...and with no exit to observe a carrier with, the comparison IS
    -- `eq?` on the carrier, and the refusal names the slot that would
    -- have decided it honestly
  , (closureModNoExit ++ "transformation Scaled : Src ⇒ Dst = toK\n1 >> print",
     "declare an exit `observe` in the theory")
    -- ...and it says WHICH exit is missing.  Until 2026-09-15 it said
    -- the theory declares no exit, full stop, which is false of a
    -- theory that declares one the slot's result does not FIT —
    -- `examples/prob.braid` is that case: `observe : k(Int, Int)` is an
    -- exit, and `first` leaves the hom-object at a PAIRING, which it
    -- does not reach.  A refusal that misreports its own cause sends
    -- the reader to the wrong repair.
  , (closureModNoExit ++ "transformation Scaled : Src ⇒ Dst = toK\n1 >> print",
     "no exit whose input FITS this slot's result")
    -- ...and with NO evidence to sample with, the refusal names the slot
    -- and asks for the slot that would decide it
  , ("theory Mag(a) =\n    op : a a ⇒ a\n\
     \model Sum : Mag(Int) =\n    op = +\n\
     \model Prod : Mag(Int) =\n    op = *\n\
     \transformation Id : Sum ⇒ Prod = id\n1 >> print",
     "transformation Id: the square for slot 'op' is FALSE — `sameCode` \
     \decides the two sides are different programs of the free category")
  , ("theory Mag(a) =\n    op : a a ⇒ a\n\
     \model Sum : Mag(Int) =\n    op = +\n\
     \model Prod : Mag(Int) =\n    op = *\n\
     \transformation Id : Sum ⇒ Prod = id\n1 >> print",
     "Add a `sample` slot to theory Mag")
    -- ...and a square decided FALSE on PURE WIRING, with no arithmetic
    -- anywhere in it: `_ drop` against `drop _` is a different program
    -- of the free category and there is nothing more to say (2026-09-14
    -- — before `fallbackFalse` went, `false` and "could not decide"
    -- were the same answer here).
  , ("theory Pick(a) =\n    pick : a a ⇒ a\n\
     \model Fst : Pick(Int) =\n    pick = _ drop\n\
     \model Snd : Pick(Int) =\n    pick = drop _\n\
     \transformation Keep : Fst ⇒ Snd = id\n1 >> print",
     "transformation Keep: the square for slot 'pick' is FALSE")
    -- two models of ONE theory, or it is not a component
  , (monoidMod ++ "theory Other(a) =\n    z : • ⇒ a\n\
     \model Zed : Other(Int) =\n    z = 0\n\
     \transformation Nope : ListMonoid ⇒ Zed = len\n1 >> print",
     "ListMonoid models Monoid and Zed models Other: a transformation is \
     \a component between two models of ONE theory")
    -- and the component's own type is the two carriers, read off the
    -- model heads
  , (monoidMod ++ "transformation Nope : ListMonoid ⇒ IntSum = toStr\n\
     \1 >> print",
     "transformation Nope: the square for slot 'unit' does not typecheck")
    -- THE DOCTRINE'S LAWS RUN, for a model in another file.  This
    -- carrier is a function AND a counter, and its composition charges
    -- one per `;` — parametric enough to typecheck, and wrong, so the
    -- prelude's `leftId` catches it.  (Most wrong models of an arrow
    -- theory never get this far: the hom-object's parameters are
    -- universally quantified, so a composition in the wrong order or a
    -- `first` that swaps the pair is refused by the SIGNATURE.)
  , ("data Ctr(a, b) = Fn⟨a ⇒ b⟩ Int\n\
     \theory Counting(k(_, _)) over Doctrine =\n\
     \    embed   : Fn⟨a ⇒ b⟩ ⇒ k(a, b)\n\
     \    compose : k(a, b) k(b, c) ⇒ k(a, c)\n\
     \    observe : k(Int, Int) ⇒ Int\n\
     \    sample  : • ⇒ k(Int, Int)\n\
     \model Counted : Counting(Ctr) =\n\
     \    embed   = (f -> f 0 ; Ctr)\n\
     \    compose = (c d -> c ; unCtr ; (f m -> d ; unCtr ; (g n -> [(x -> f ; _ x ; ev ; (y -> g ; _ y ; ev))] (m n ; + ; _ 1 ; +) ; Ctr)))\n\
     \    observe = (c -> c ; unCtr ; drop _)\n\
     \    sample  = [dup ; +] 0 ; Ctr\n1 ; print",
     "law 'leftId' fails for model Counted")
    -- extension is one level deep: a doctrine of a doctrine wants a
    -- pushout nobody has asked for
  , ("data W(a, b) = Fn⟨a ⇒ b⟩\n\
     \theory Mid(k(_, _)) over Doctrine =\n\
     \    compose : k(a, b) k(b, c) ⇒ k(a, c)\n\
     \theory Top(k(_, _)) over Mid =\n\
     \    compose : k(a, b) k(b, c) ⇒ k(a, c)\n1 ; print",
     "extends a theory that itself extends Doctrine, and extension is \
     \one level deep")
    -- one category per header: the second would embed the first's
    -- carriers as if they were programs
  , (modeMod ++ "def bad = use Funcs Funcs2 ; add1\nbad ; drop",
     "a header may name at most one category")
    -- THE FLAGSHIP QUESTION (plan item 4c): a word of one category
    -- inside ANOTHER's scope.  It does NOT type — an embedding embeds a
    -- program and a carrier is not one — and inference would say
    -- `• vs a16`, so the elaborator says it instead.
  , (modeMod ++ "def other = use Funcs2 ; add1\n\
     \def bad = use Funcs ; chain ; other\nbad ; drop",
     "other is a word of Funcs2, so it builds a carrier rather than \
     \being a program embed could embed")
  ]

runPass :: (String, String) -> Maybe String
runPass (src, expected) =
  case inferNormalized src of
    Left err -> Just $ show src ++ ": expected " ++ expected ++ ", got error: " ++ err
    Right arr
      | show arr == expected -> Nothing
      | otherwise ->
          Just $ show src ++ ": expected " ++ expected ++ ", got " ++ show arr

runFail :: (String, String) -> Maybe String
runFail (src, fragment) =
  case inferProgram src of
    Right arr ->
      Just $ show src ++ ": expected failure containing " ++ show fragment
           ++ ", but inferred " ++ show arr
    Left err
      | fragment `isInfixOf` err -> Nothing
      | otherwise ->
          Just $ show src ++ ": expected error containing " ++ show fragment
               ++ ", got: " ++ err

runModuleType :: (String, String) -> Maybe String
runModuleType (src, expected) =
  case checkModule src of
    Left err -> Just $ show src ++ ": expected " ++ expected ++ ", got error: " ++ err
    Right m ->
      case modMain m of
        Nothing -> Just $ show src ++ ": module has no main program"
        Just (_, arr)
          | rendered == expected -> Nothing
          | otherwise ->
              Just $ show src ++ ": expected " ++ expected
                   ++ ", got " ++ rendered
          where rendered = showArrowA (Disp (modAliases m)
                                   [ dName d | d <- modDatas m, dResource d ]
                                   [ (tpName md, tpCarrier md) | md <- modTrans m ])
                            (normalizeArrow arr)

runEval :: (String, [String], String) -> IO (Maybe String)
runEval (src, wantLog, wantStack) = do
  r <- runModule src
  pure $ case r of
    Left err -> Just $ show src ++ ": runtime/type error: " ++ err
    Right (stack, logs)
      | logs == wantLog && unwords (map show stack) == wantStack -> Nothing
      | otherwise ->
          Just $ show src ++ ": expected log " ++ show wantLog
               ++ " stack " ++ show wantStack
               ++ ", got log " ++ show logs
               ++ " stack " ++ show (unwords (map show stack))

runModuleNoHint :: (String, String) -> IO (Maybe String)
runModuleNoHint (src, fragment) = do
  r <- runModule src
  pure $ case r of
    Right _ ->
      Just $ show src ++ ": expected a failure, but it ran"
    Left err
      | fragment `isInfixOf` err ->
          Just $ show src ++ ": message must NOT contain " ++ show fragment
               ++ ", got: " ++ err
      | otherwise -> Nothing

runModuleFail :: (String, String) -> IO (Maybe String)
runModuleFail (src, fragment) = do
  r <- runModule src
  pure $ case r of
    Right (stack, logs) ->
      Just $ show src ++ ": expected failure containing " ++ show fragment
           ++ ", but ran with stack " ++ show (unwords (map show stack))
           ++ " log " ++ show logs
    Left err
      | fragment `isInfixOf` err -> Nothing
      | otherwise ->
          Just $ show src ++ ": expected error containing " ++ show fragment
               ++ ", got: " ++ err

--------------------------------------------------------------------------------
-- Exponent unification (stage 1–2 of design-exponents.md): no surface
-- syntax yet, so these drive unifyStack/unifyExp directly.  On success
-- the invariant is ev s a == ev s b (the unifier really unified).
--------------------------------------------------------------------------------

unifTests :: [(String, SType, SType, Bool)]
unifTests =
  [ ("Int^n ~ Int Int Int (n:=3)",     expN "n" intS,  ints 3,          True)
  , ("Int^n ~ • (n:=0)",               expN "n" intS,  SEnd,            True)
  , ("Int^n ~ Int Str Int",            expN "n" intS,  SCons TInt (SCons TStr (SCons TInt SEnd)), False)
  , ("Int^n ~ Int Int rho (bridge)",   expN "n" intS,  SCons TInt (SCons TInt (STail (SV "rho"))), True)
  , ("Int^n ~ rho (tail binds whole)", expN "n" intS,  STail (SV "rho"), True)
  , ("Int^n ~ Int^m (n~m)",            expN "n" intS,  expN "m" intS,   True)
  , ("Int^(n+1) ~ Int Int Int (n:=2)", SExp intS (Exp 1 (Just (NV "n"))) SEnd, ints 3, True)
  , ("Int^(n+1) ~ • (impossible)",     SExp intS (Exp 1 (Just (NV "n"))) SEnd, SEnd, False)
  , ("(Int Str)^n ~ Int Str Int Str",  expN "n" istS,  SCons TInt (SCons TStr (SCons TInt (SCons TStr SEnd))), True)
  , ("(Int Str)^n ~ Int Str Int (odd width)", expN "n" istS, SCons TInt (SCons TStr (SCons TInt SEnd)), False)
  , ("a^n ~ Int Int (copies share a)", expN "n" (SCons (TVarTy (TV "a")) SEnd), ints 2, True)
  , ("a^n ~ Int Str (copies clash)",   expN "n" (SCons (TVarTy (TV "a")) SEnd), SCons TInt (SCons TStr SEnd), False)
  , ("Int^n Str ~ Int Int Str (rest anchored)", expNr "n" intS (SCons TStr SEnd), SCons TInt (SCons TInt (SCons TStr SEnd)), True)
  , ("Int^n Str ~ Int Int (no anchor)", expNr "n" intS (SCons TStr SEnd), ints 2, False)
    -- existentials (a splice's frozen result) unify with themselves and
    -- absorb FLEXIBLE variables, but never with a concrete stack: that
    -- rigidity is what stops a caller assuming a shape for code that
    -- only exists at runtime
  , ("∃ρ ~ ∃ρ (itself)",        STail (SV "∃0"), STail (SV "∃0"), True)
  , ("∃ρ ~ ρ (absorbs a var)",  STail (SV "∃0"), STail (SV "rho"), True)
  , ("∃ρ ~ Int (rigid)",        STail (SV "∃0"), intS,             False)
  , ("∃ρ ~ • (rigid)",          STail (SV "∃0"), SEnd,             False)
  ]
  where
    intS = SCons TInt SEnd
    istS = SCons TInt (SCons TStr SEnd)
    ints k = foldr SCons SEnd (replicate k TInt)
    expN nm b = SExp b (Exp 0 (Just (NV nm))) SEnd
    expNr nm b r = SExp b (Exp 0 (Just (NV nm))) r

-- The ELABORATION-TIME evaluator: the same `evalTerm`, run purely and
-- on a step budget, which is what lets a functor be applied while a
-- module is still being checked (design-macros.md, stage 2).  Pinned
-- here because stage 3 depends on all three properties: pure programs
-- run, IO edges are unreachable, and the budget actually bites.
pureEvalTests :: [(String, Int, String, Either String String)]
pureEvalTests =
  [ ("arithmetic",   1000, "1 2 >> +",            Right "3")
  , ("quote/ev",  1000, "[dup >> *] >> _ 5 >> ev", Right "25")
  , ("list library", 1000, "(1 2 3 >> pack) >> [+] 0 ... >> fold", Right "6")
    -- `print` is NOT an IO edge: it accumulates into the returned log,
    -- so it stays pure here (its io GRADE is what keeps it out of a
    -- functor).  The real edges are readLine/readFile/writeFile, and
    -- reaching one during elaboration says so rather than lying —
    -- unreachable in practice, since a functor is checked pure first.
  , ("print is pure",  1000, "\"x\" >> print",  Right "")
  , ("io unreachable", 1000, "readLine >> (pass | pass) >> merge",
     Left "IO edge was reached")
    -- purity is not totality: the budget is the only thing standing
    -- between a looping functor and a hung compiler
  , ("budget bites",      3, "1 2 >> + >> 3 >> + >> 4 >> +",
     Left "step budget exhausted")
  ]

runPureE :: (String, Int, String, Either String String) -> Maybe String
runPureE (nm, fuel, src, expected) =
  let got = do
        t0 <- parseProgram src
        t1 <- elabUseWith (elabCtx0 (modEnv preludeModule) []) t0
        (out, _) <- runPureEvalWith fuel
                      (evalTerm (modEnv preludeModule)
                                (moduleRunDefs preludeModule) emptyVarEnv t1 [])
        pure (unwords (map show out))
  in case (expected, got) of
       (Right want, Right have) | want == have -> Nothing
       (Left frag, Left err) | frag `isInfixOf` err -> Nothing
       _ -> Just $ nm ++ ": expected " ++ show expected ++ ", got " ++ show got

runUnif :: (String, SType, SType, Bool) -> Maybe String
runUnif (name, a, b, wantOk) =
  case unifyStack emptySubst a b of
    Left err
      | wantOk    -> Just $ name ++ ": expected success, got: " ++ err
      | otherwise -> Nothing
    Right s
      | not wantOk -> Just $ name ++ ": expected failure, but unified to "
                           ++ show (apply s a)
      | apply s a == apply s b -> Nothing
      | otherwise -> Just $ name ++ ": unified but applied sides differ: "
                          ++ show (apply s a) ++ " vs " ++ show (apply s b)

main :: IO ()
main = do
  evalFs <- mapM runEval evalTests
  mfailFs <- mapM runModuleFail moduleFailTests
  nohintFs <- mapM runModuleNoHint moduleNoHintTests
  exNames <- sort . filter (".braid" `isSuffixOf`) <$> listDirectory "examples"
  exFs <- mapM runExample exNames
  impFs  <- mapM runImport importTests
  impFFs <- mapM runImportFail importFailTests
  tbFs   <- mapM runTable tableTests
  tbFFs  <- mapM runTableFail tableFailTests
  tbIFs  <- mapM runTableImport tableImportTests
  mvFs   <- mapM runTransformationVerdicts transformationVerdictTests
  let famFs = map runFamilyReport familyReportTests
  let failures = concatMap (maybe [] pure)
        (  map runPass passTests
        ++ map runFail failTests
        ++ map runModuleType moduleTypeTests
        ++ evalFs
        ++ mfailFs
        ++ nohintFs
        ++ map runUnif unifTests
        ++ map runPureE pureEvalTests
        ++ exFs
        ++ impFs
        ++ impFFs
        ++ tbFs
        ++ tbFFs
        ++ tbIFs
        ++ mvFs
        ++ famFs
        )
      total = length passTests + length failTests
            + length moduleTypeTests + length evalTests + length moduleFailTests
            + length moduleNoHintTests
            + length unifTests + length pureEvalTests + length exNames
            + length importTests + length importFailTests
            + length tableTests + length tableFailTests
            + length tableImportTests
            + length transformationVerdictTests
            + length familyReportTests
  mapM_ (putStrLn . ("FAIL " ++)) failures
  putStrLn $ show (total - length failures) ++ "/" ++ show total ++ " tests passed"
  if null failures then exitSuccess else exitFailure
