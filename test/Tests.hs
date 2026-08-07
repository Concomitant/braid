-- Test suite: run via `cabal test`.
module Main (main) where

import MiniConcatTypechecker
import Data.List (isInfixOf, isSuffixOf, sort)
import System.Exit (exitFailure, exitSuccess)
import System.Directory (listDirectory)

-- Every examples/*.braid must run without error (catches rot: an
-- unknown prim, a type error, a desync).  Output-regression checking
-- is a future enhancement; "runs clean" is the high-value signal.
runExample :: String -> IO (Maybe String)
runExample name = do
  src <- readFile ("examples/" ++ name)
  r   <- runModule src
  pure $ case r of
    Right _  -> Nothing
    Left err -> Just ("examples/" ++ name ++ ": " ++ err)

-- (source, expected alpha-normalized type)
passTests :: [(String, String)]
passTests =
  [ -- literals are terminal-source constants (• ⇒ Int, no implicit remainder)
    ("17",            "• ⇒ Int")
  , ("1 2",           "• ⇒ Int Int")
  , ("1 2 3",         "• ⇒ Int Int Int")
  , ("1 ...",         "ρ0 ⇒ Int ρ0")     -- explicit remainder: push onto any stack
    -- pushing over existing wires: id covers exactly one, ... covers any
  , ("2 id",          "a0 ⇒ Int a0")
  , ("1 >> 2 id",     "• ⇒ Int Int")
  , ("1 >> 2 ...",    "• ⇒ Int Int")
  , ("1 >> 2 \8230",  "• ⇒ Int Int")   -- U+2026 … aliases ...
  , ("+",             "Int Int ⇒ Int")
  , ("pass",          "ρ0 ⇒ ρ0")

    -- cartesian basis (exact: no implicit remainder on operations either)
  , ("swap",          "a0 a1 ⇒ a1 a0")
  , ("dup",           "a0 ⇒ a0 a0")
  , ("drop",          "a0 ⇒ •")
  , ("id",            "a0 ⇒ a0")
    -- _ is id: the section hole — marks where the incoming wire goes
  , ("_",             "a0 ⇒ a0")
  , ("2 _ >> *",      "Int ⇒ Int")
  , ("_ 2 >> -",      "Int ⇒ Int")
  , ("_ drop",        "a0 a1 ⇒ a0")

    -- sequencing; increment needs the explicit remainder (1 >> + is ill-typed)
  , ("1 ... >> +",    "Int ⇒ Int")
  , ("1 2 >> +",      "• ⇒ Int")
    -- strict tensor: `1 +` is (• ⇒ Int) ⊗ (Int Int ⇒ Int), NOT increment
  , ("1 +",           "Int Int ⇒ Int Int")
  , ("1 2 >> (1 ... >> +) (2 _ >> *) >> + >> print", "• ⇒ •")

    -- newline is strict >>
  , ("1 2\n(1 ... >> +) (2 _ >> *)\n+\nprint", "• ⇒ •")
  , ("1 2\n\n+",                 "• ⇒ Int")   -- blank lines collapse
    -- ; is a synonym for >>
  , ("1 2 ; +",                  "• ⇒ Int")
  , ("dup ; * ; toStr",          "Int ⇒ Str")
  , ("5;dup;*",                  "• ⇒ Int")   -- no whitespace needed

    -- worked schemes from the spec (now exact, matching it verbatim)
  , ("dup >> *",      "Int ⇒ Int")           -- square
  , ("id drop",       "a0 a1 ⇒ a0")          -- first
  , ("dup >> id drop","a0 ⇒ a0")             -- counit law
  , ("dup >> swap",   "a0 ⇒ a0 a0")          -- commutativity law
  , ("swap >> swap",  "a0 a1 ⇒ a0 a1")       -- involution

    -- trailing remainder: ... and >>> (ops are exact, so deep stacks need it too)
  , ("1 2 3 >> (1 ... >> +) ... >> + ...",  "• ⇒ Int Int")
  , ("1 2 3 >> (1 ... >> +) >>> + ...",     "• ⇒ Int Int")   -- >>> ≡ the ... form
  , ("1 2 3\n(1 ... >> +) ...\n+ ...", "• ⇒ Int Int")   -- same, via newlines
  , ("...",                      "ρ0 ⇒ ρ0")       -- bare remainder stage

    -- quotations and apply (quotes are terminal-source constants)
  , ("[dup >> *]",               "• ⇒ Fn⟨Int ⇒ Int⟩")
  , ("[dup >> *] 7 >> apply",    "• ⇒ Int")
  , ("[dup >> *] 7 >> apply >> print", "• ⇒ •")   -- spec example (49)
  , ("apply",                    "Fn⟨ρ0 ⇒ ρ1⟩ ρ0 ⇒ ρ1")

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
  , ("in1",           "ρ0 ⇒ (ρ0 | σ0)")
  , ("in2",           "ρ0 ⇒ (ρ1 | ρ0 | σ0)")
    -- compositional injections: here starts a sum, there widens it;
    -- here >> there ≡ in2, exactly
  , ("here",          "ρ0 ⇒ (ρ0 | σ0)")
  , ("there",         "(σ0) ⇒ (ρ0 | σ0)")
  , ("here >> there", "ρ0 ⇒ (ρ1 | ρ0 | σ0)")
  , ("1 2 >> in1",    "• ⇒ (Int Int | σ0)")
  , ("merge",         "(ρ0 | ρ0) ⇒ ρ0")
  , ("(dup | drop)",  "(a0 | a1) ⇒ (a0 a0 | •)")
  , ("(dup | ...)",   "(a0 | σ0) ⇒ (a0 a0 | σ0)")
  , ("5 >> in1 >> (dup >> * | ...) >> merge", "• ⇒ Int")
  , ("[dup >> * | drop]", "• ⇒ Fn⟨(Int | a0) ⇒ (Int | •)⟩")
    -- case(…): the coproduct eliminator — one handler per nested track,
    -- all landing on a common result.  Branches are full programs, bare.
    -- (associators, which need the prelude, are in moduleTypeTests.)
  , ("case(dup >> +)",                          "Int ⇒ Int")
  , ("case(drop >> \"neg\", drop >> \"zero\", toStr)", "(a0 | (a1 | a2)) ⇒ Str")
  , ("case(dup >> +, drop >> 3)",               "(Int | a0) ⇒ Int")
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
  , ("dup | +",                  "(a0 | Int Int) ⇒ (a0 a0 | Int)")
  , ("dup | +\n+ | id\nmerge",   "(Int | Int Int) ⇒ Int")
  , ("1 ... >> + | ...",         "(Int | σ0) ⇒ (Int | σ0)")

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
  , ("loop",          "Fn⟨ρ0 ⇒ (ρ0 | ρ1)⟩ ρ0 ⇒ ρ1")
    -- loop protocol aliases: again ≡ in1 (continue), done ≡ in2 (exit)
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
  , ("dup >> apply",  "Occurs check")
  , ("[dup",          "Unclosed quotation")
  , ("]",             "Expected a tensor stage")
  , ("(1",            "Unclosed group")
    -- list elements must be pure pushes
  , ("list(1, 2)",   "Unclosed group")   -- the literal is GONE: bare ident + a comma in a group
  , ("dup ... drop",       "'...' must be the final atom")
  , ("1 >",           "Unexpected '>'")
    -- a newline is a strict >>, so a trailing >> before one is >> >>:
    -- the continuation-absorption rule was ditched for >> and | (it
    -- survives only for >=>, >?>, >!>, ||, which a newline can't express)
  , ("1 2 >>\n+",     "Expected a tensor stage")
  , ("nonsense42x",   "Unknown primitive")
  , ("",              "Expected a tensor stage")
    -- sums
  , ("5 >> in1 >> (1 | ...)",  "Cannot unify stacks")   -- alt • vs Int
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
  ]

-- (module source, expected alpha-normalized type of main)
moduleTypeTests :: [(String, String)]
moduleTypeTests =
  [ ("def square = dup >> *\nsquare",           "Int ⇒ Int")
    -- >=> is Kleisli composition in the sum monad
  , ("even? >=> zero?",                         "Int ⇒ (Int | Int)")
    -- routers, now derived in the prelude from eq?/lt?/mod via the
    -- (n | n) pattern — same closed types as the old prims
  , ("negative?",     "Int ⇒ (Int | Int)")
  , ("odd?",          "Int ⇒ (Int | Int)")
  , ("zero?",         "Int ⇒ (Int | Int)")
    -- sum associators re-nest a decision tree (open tails from in1/in2)
  , ("assocL", "(ρ0 | (ρ1 | ρ2)) ⇒ ((ρ0 | ρ1 | σ0) | ρ2 | σ1)")
  , ("assocR", "((ρ0 | ρ1) | ρ2) ⇒ (ρ0 | (ρ1 | ρ2 | σ0) | σ1)")
    -- type aliases: display folding (Bool/Maybe from the prelude;
    -- user aliases beat prelude; fewest-params-bound wins ties)
  , ("5 >> odd? >> verdict",                    "• ⇒ Bool")
  , ("7 >> zero? >> (forget | ...)",            "• ⇒ Maybe(Int)")
  , ("type MInt = (• | Int)\n7 >> zero? >> (forget | ...)", "• ⇒ MInt")
  , ("type Result(a, e) = (a | e)\nodd?",       "Int ⇒ Result(Int, Int)")
  , ("type YN = Bool\ntrue",                    "• ⇒ YN")
    -- Fn in type declarations: alias naming + display folding, both
    -- the Unicode (Fn⟨…⟩) and ASCII (Fn(… -> …)) spellings
  , ("type Endo(a) = Fn⟨a ⇒ a⟩\n[dup >> *]",     "• ⇒ Endo(Int)")
  , ("type Endo(a) = Fn(a -> a)\n[dup >> *]",     "• ⇒ Endo(Int)")
  , ("type Pred(a) = Fn⟨a ⇒ (a | a)⟩\n[odd?]",    "• ⇒ Pred(Int)")
    -- a param substituted INSIDE the Fn (substStackVars into TFn), and
    -- folded back on display
  , ("type Thunk(a) = Fn⟨• ⇒ a⟩\n[5]",            "• ⇒ Thunk(Int)")
    -- codata: recursion THROUGH a Fn makes the type nominal; the
    -- constructor carries the thunked tail
  , ("data Stream(a) = (a Fn⟨• ⇒ Stream(a)⟩)\nStream",
        "ρ0 Fn⟨• ⇒ Stream(ρ0)⟩ ⇒ Stream(ρ0)")
    -- pack: list introduction from a bundle — (elements ; pack) replaces
    -- the list(…) special form; elements are full programs, groups delimit
  , ("(1 2 3 >> pack)",          "• ⇒ List(Int)")
  , ("(pack)",                   "a0ⁿ⁰ ⇒ List(a0)")   -- final position: open
  , ("(1 \"a\" 2 \"b\" >> pack2)", "• ⇒ List(Int Str)")
    -- exponent syntax in type declarations: literal ^k (and Unicode
    -- superscript input) expands to k copies; segments repeat wholesale
  , ("type T3 = (Int^3 | Str)\n1 2 3 >> in1 >> (pass | drop >> \"x\")", "• ⇒ T3")
  , ("type W = (• | Int³)\n1 2 3 >> in2 >> (forget | pass)", "• ⇒ W")
  , ("type PP = ((Int Str)^2 | •)\n1 \"a\" 2 \"b\" >> in1 >> (pass | forget)", "• ⇒ PP")
    -- foldExp: the exponent eliminator — variadic folds over bare stack
    -- products; n is erased and generalizes per def
  , ("[+] 0 ... >> foldExp",                    "Intⁿ⁰ ⇒ Int")
  , ("def total = [+] 0 ... >> foldExp\ntotal", "Intⁿ⁰ ⇒ Int")
    -- GLA generators: width-polymorphic wiring over bundles
  , ("dupN",   "a0ⁿ⁰ ⇒ a0ⁿ⁰ a0ⁿ⁰")
  , ("addN",   "Intⁿ⁰ Intⁿ⁰ ⇒ Intⁿ⁰")
  , ("zipN",   "a0ⁿ⁰ a1ⁿ⁰ ⇒ (a0 a1)ⁿ⁰")
  , ("sumN",   "Intⁿ⁰ ⇒ Int")
  , ("firstTrue", "((• | •) Fn⟨• ⇒ ρ0⟩)ⁿ⁰ Fn⟨• ⇒ ρ0⟩ ⇒ ρ0")
    -- (before the grouped-compound constraint fix this leaked fake
    -- polymorphism: a0ⁿ a1ⁿ ⇒ Int, crashing on non-Int bundles)
  , ("def dot = zipN >> [(acc a b -> (a b >> *) acc >> +)] 0 ... >> foldExp2\ndot", "Intⁿ⁰ Intⁿ⁰ ⇒ Int")
    -- two-tier control flow: p? routes and keeps, bare p forgets to Bool
  , ("equals",                                  "a0 a0 ⇒ Bool")
  , ("less",                                    "Int Int ⇒ Bool")
  , ("odd",                                     "Int ⇒ Bool")
  , ("equals?",                                 "a0 a0 ⇒ (a0 | a0)")
    -- recursive type declarations: nominal, Name rolls / Name? unrolls
    -- the printer folds Nat's unfolding to Maybe(Nat) — which is the
    -- theorem: Nat ≅ Maybe(Nat) is the successor algebra
  , ("type Nat = (• | Nat)\nunNat",              "Nat ⇒ Maybe(Nat)")
  , ("type Nat = (• | Nat)\nNat",               "Maybe(Nat) ⇒ Nat")
  , ("type Tree(a) = (a | Tree(a) Tree(a))\nunTree", "Tree(ρ0) ⇒ (ρ0 | Tree(ρ0) Tree(ρ0))")
    -- data keyword: nominal without recursion; single-alternative
    -- bodies get doors against the field stack
  , ("data Person = (Str Int)\nPerson",         "Str Int ⇒ Person")
  , ("data Person = (Str Int)\nunPerson",       "Person ⇒ Str Int")
  , ("data Flag = (• | •)\nunFlag",             "Flag ⇒ Bool")
    -- generated folds: definition by points (recursive slots pre-folded)
  , ("type Nat = (• | Nat)\nfoldNat", "Fn⟨• ⇒ ρ0⟩ Fn⟨ρ0 ⇒ ρ0⟩ Nat ⇒ ρ0")
    -- List is now a declared type in the prelude; the library is derived
  , ("uncons",  "List(ρ0) ⇒ (• | ρ0 List(ρ0))")
  , ("cons",    "ρ0 List(ρ0) ⇒ List(ρ0)")
    -- stack-kinded parameters: zip without Pair
  , ("zip",     "List(a0) List(a1) ⇒ List(a0 a1)")
  , ("map",     "Fn⟨a0 ⇒ a1⟩ List(a0) ⇒ List(a1)")
  , ("fold",    "Fn⟨a0 a1 ⇒ a0⟩ a0 List(a1) ⇒ a0")
  , ("def square = dup >> *\nsquare >> square", "Int ⇒ Int")
  , ("def first = id drop\n1 2 >> first",       "• ⇒ Int")
    -- one def used at two different types = let-polymorphism
  , ("def discard = drop\n1 discard >> true discard", "a0 ⇒ Bool")
    -- recursive defs (monomorphic self-reference)
  , ("def decr = _ 1 >> -\ndef lt2? = _ 2 >> lt? >> (_ drop | _ drop)\ndef fib = lt2? >> (_ | (n -> n >> decr >> fib >> _ (n 2 >> - >> fib) >> +)) >> merge\nfib", "Int ⇒ Int")
  ]

-- (module source, expected print log, expected final stack rendering)
evalTests :: [(String, [String], String)]
evalTests =
  [ ("1 2 >> (1 ... >> +) (2 _ >> *) >> + >> print", ["6"],  "")   -- succ, double
  , ("1 2 >> swap",                        [],     "2 1")
  , ("1 2 3 >> (1 ... >> +) ... >> + ...",   [],     "4 3")
  , ("1 2 3 >> (1 ... >> +) >>> + ...",      [],     "4 3")
  , ("def square = dup >> *\n5 >> square >> print", ["25"], "")
  , ("true false",                         [],     "in1() in2()")
  , ("1 2\nswap\nprint ...\nprint",        ["2", "1"], "")
  , ("1\n2 id",                            [],     "2 1")
  , ("1\n2 ...",                           [],     "2 1")

    -- quotations and apply
  , ("[dup >> *] 7 >> apply >> print",     ["49"], "")   -- from the spec
  , ("[1 2 >> +] >> apply >> print",       ["3"],  "")
  , ("[pass]",                             [],     "[fn]")
  , ("def sq = [dup >> *]\nsq 5 >> apply", [],     "25")
    -- tails-only closing: a non-final def keeps its element-internal
    -- polymorphism (q's quoted pass applies to whatever follows)
  , ("def q = [pass]\nq 1 >> apply",        [],     "1")

  , ("5 >> negative?",                     [],     "in2(5)")

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
  , ("7 >> (x -> [x 1 >> +]) >> apply >> print",   ["8"], "")

    -- sums: injections, code rows, merge
  , ("5 >> in1 >> (dup >> * | ...) >> merge >> print",       ["25"], "")
  , ("7 >> in2 >> (dup >> * | 1 ... >> +) >> merge >> print", ["8"], "")
  , ("5 >> in2 >> (drop | ...)",           [],     "in2(5)")
  , ("1 2 >> in1",                         [],     "in1(1, 2)")
  , ("3 4 >> here >> there",               [],     "in2(3, 4)")
    -- decide-then-inject: predicate is already the fork (Bool ≡ (• | •))
  , ("def classify = even? >> (here | here >> there) >> merge\n4 >> classify",
                                           [],     "in1(4)")
  , ("def classify = even? >> (here | here >> there) >> merge\n5 >> classify",
                                           [],     "in2(5)")
    -- routers in flight: quoted routers dispatch via plain apply
  , ("5 >> [odd?] ... >> apply",           [],     "in1(5)")
  , ("4 >> [odd?] ... >> apply",           [],     "in2(4)")
    -- if-then-else is route >> row >> merge
  , ("5 >> odd? >> (id | drop >> 0) >> merge >> print", ["5"], "")
  , ("4 >> odd? >> (id | drop >> 0) >> merge >> print", ["0"], "")
    -- loop: Elgot iteration (sum 1..5)
  , ("def decr = (x -> x 1 >> -)\ndef sumStep = (a n -> n >> zero? >> ((z -> a >> done) | (m -> (a m >> +) (m >> decr) >> again)) >> merge)\n0 5 >> [sumStep] ... >> loop >> print", ["15"], "")
    -- the guard machine as a loop body
  , ("0 3 >> [(a n -> n >> zero? >> ((z -> a >> done) | (m -> (a m >> +) (m 1 >> -) >> again)) >> merge)] ... >> loop >> print", ["6"], "")
  , ("5 3 >> - >> print",                  ["2"],  "")
  , ("7 >> (2 _ >> *) >> print",           ["14"], "")
    -- multi-line def bodies + recurse (anonymous self-reference)
  , ("def lt100? = _ 100 >> lt? >> (_ drop | _ drop)\ndef double = 2 _ >> *\ndef until100 =\n  lt100?\n  double >> recurse | _\n  merge\n7 >> until100 >> print", ["112"], "")
  , ("def decr = _ 1 >> -\ndef lt2? = _ 2 >> lt? >> (_ drop | _ drop)\ndef fib =\n  lt2?\n  _ | (n -> n >> decr >> recurse >> _ (n 2 >> - >> recurse) >> +)\n  merge\n10 >> fib >> print", ["55"], "")
    -- while, DERIVED in-language: whileFn assembles the loop body
    -- from closures; while = whileFn ... >> loop fuses in the knot
  , ("def lt100? = _ 100 >> lt? >> (_ drop | _ drop)\ndef double = 2 _ >> *\ndef whileFn = (p f -> [p ... >> apply >> (f ... >> apply >> again | done) >> merge])\ndef while = whileFn ... >> loop\n7 >> [lt100?] [double] ... >> while >> print", ["112"], "")
  , ("def lt100? = _ 100 >> lt? >> (_ drop | _ drop)\ndef double = 2 _ >> *\ndef whileFn = (p f -> [p ... >> apply >> (f ... >> apply >> again | done) >> merge])\ndef while = whileFn ... >> loop\n7 >> [lt100?] [double >> double] ... >> while >> print", ["112"], "")
    -- comments: # to end of line, ## docs are inert at runtime
  , ("# header comment\n5 >> print # trailing", ["5"], "")
  , ("## doc for sq2\ndef sq2 = dup >> *\n3 >> sq2 >> print", ["9"], "")
  , ("type MInt = (• | Int)\n5 >> print",        ["5"], "")
    -- data at runtime: bundle, spill, use
  , ("data Person = (Str Int)\n\"ada\" 36 >> Person >> unPerson >> _ drop >> print", ["ada"], "")
  , ("data Person = (Str Int)\n\"ada\" 36 >> Person >> unPerson >> drop ... >> print", ["36"], "")
    -- Peano round-trip: folds by ordinary recursion through unNat
  , ("type Nat = (• | Nat)\ndef fromInt = zero? >> (drop >> in1 >> Nat | _ 1 >> - >> fromInt >> in2 >> Nat) >> merge\ndef toInt = unNat >> (0 | toInt >> 1 ... >> +) >> merge\n3 >> fromInt >> toInt >> print", ["3"], "")
    -- trees: build with rolled injections, fold with recursion
  , ("type Tree(a) = (a | Tree(a) Tree(a))\ndef leaf = in1 >> Tree\ndef node = in2 >> Tree\ndef total = unTree >> (_ | _ total >> swap >> _ total >> +) >> merge\n1 >> leaf >> _ (2 >> leaf) >> node >> _ (4 >> leaf) >> node >> total >> print", ["7"], "")
    -- same folds, by points: [case1] [case2] ... >> foldName
  , ("type Nat = (• | Nat)\ndef fromInt = zero? >> (drop >> in1 >> Nat | _ 1 >> - >> fromInt >> in2 >> Nat) >> merge\n3 >> fromInt >> [0] [1 ... >> +] ... >> foldNat >> print", ["3"], "")
  , ("type Tree(a) = (a | Tree(a) Tree(a))\ndef leaf = in1 >> Tree\ndef node = in2 >> Tree\n1 >> leaf >> _ (2 >> leaf) >> node >> _ (4 >> leaf) >> node >> [_] [+] ... >> foldTree >> print", ["7"], "")
  , ("type Tree(a) = (a | Tree(a) Tree(a))\ndef leaf = in1 >> Tree\ndef node = in2 >> Tree\n1 >> leaf >> _ (2 >> leaf) >> node >> _ (4 >> leaf) >> node >> [drop >> 1] [+] ... >> foldTree >> print", ["3"], "")
    -- prelude defs available with no local definition
  , ("5 >> _ 5 >> equals? >> print",             ["in1(5)"], "")
  , ("def double = 2 _ >> *\n7 >> [_ 100 >> less?] [double] ... >> while >> print", ["112"], "")
  , ("7 >> [_ 100 >> less? >> not] [dup >> +] ... >> until >> print", ["112"], "")
    -- user defs shadow prelude defs
  , ("def while = drop\n1 2 >> while ... >> print", ["2"], "")
    -- >=>: short-circuiting Kleisli chains; in1 lifts pure stages
  , ("4 >> (even? >=> zero?) >> print",         ["in2(4)"], "")
  , ("0 >> (even? >=> zero?) >> print",         ["in1(0)"], "")
  , ("7 >> (even? >=> zero?) >> print",         ["in2(7)"], "")
  , ("def double = 2 _ >> *\n4 >> (even? >=> _ 100 >> less? >=> double >> in1) >> print", ["in1(8)"], "")
  , ("def double = 2 _ >> *\n120 >> (even? >=> _ 100 >> less? >=> double >> in1) >> print", ["in2(120)"], "")
  , ("def double = 2 _ >> *\n7 >> (even? >=> _ 100 >> less? >=> double >> in1) >> print", ["in2(7)"], "")
  , ("5 >> (_ 5 >> equals? >=> odd?) >> print",  ["in1(5)"], "")
    -- ok/miss aliases: return and stay-missed of the sum monad
  , ("def double2 = 2 _ >> *\ndef process = even? >=> _ 100 >> less? >=> double2 >> ok\n4 >> process >> print", ["in1(8)"], "")
  , ("7 >> odd? >> (ok | zero?) >> merge >> print", ["in1(7)"], "")
    -- forget (terminal morphism) and verdict: routers to pure decisions
  , ("1 2 3 >> forget", [], "")
  , ("5 >> odd? >> verdict >> print", ["in1()"], "")
  , ("4 >> odd? >> verdict >> print", ["in2()"], "")
  , ("3 4 >> eq? >> verdict >> print", ["in2()"], "")
  , ("4 4 >> eq? >> verdict >> print", ["in1()"], "")
  , ("3 3 >> equals >> print",  ["in1()"], "")
  , ("5 3 >> less >> print",    ["in2()"], "")
  , ("3 5 >> less >> print",    ["in1()"], "")
  , ("7 >> odd >> print",       ["in1()"], "")
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
  , (".red .red >> eq? >> verdict >> print", ["in1()"], "")
  , (".red .blue >> eq? >> verdict >> print", ["in2()"], "")
  , ("\"42\" >> asInt? >> print", ["in1(42)"], "")
  , ("\"4x\" >> asInt? >> print", ["in2(4x)"], "")
    -- REAL column sniffing now: strings in, typed column or evidence out
  , ("(\"1\" \"2\" \"3\" >> pack) >> [asInt?] ... >> map >> sequence >> print", ["in1(list(1, 2, 3))"], "")
  , ("(\"1\" \"x\" \"3\" >> pack) >> [asInt?] ... >> map >> sequence >> print", ["in2(x)"], "")
    -- sequence: the List/Sum distributive law — column sniffing is
    -- map parse-router >> sequence
  , ("(1 3 5 >> pack) >> [odd?] ... >> map >> sequence >> print", ["in1(list(1, 3, 5))"], "")
  , ("(1 4 5 >> pack) >> [odd?] ... >> map >> sequence >> print", ["in2(4)"], "")
    -- >?> / >!> : guard chains along the miss track (dual of >=>)
    -- asymmetric guard predicates: hit carries nothing (drop-free
    -- actions); infers as Int => Maybe(Int)
  , ("def by3? = (n -> n 3 >> mod >> zero >> (... | n))\ndef fz = by3? >> (\"fizz\" | ...) >!> toStr\n9 >> fz >> print", ["fizz"], "")
  , ("def by3? = (n -> n 3 >> mod >> zero >> (... | n))\ndef fz = by3? >> (\"fizz\" | ...) >!> toStr\n7 >> fz >> print", ["7"], "")
  , ("def by3? = (n -> n 3 >> mod >> zero >> (n | n))\ndef fz = by3? >> (drop >> \"fizz\" | ...) >!> toStr\n9 >> fz >> print", ["fizz"], "")
  , ("def by3? = (n -> n 3 >> mod >> zero >> (n | n))\ndef fz = by3? >> (drop >> \"fizz\" | ...) >!> toStr\n7 >> fz >> print", ["7"], "")
  , ("def by3? = (n -> n 3 >> mod >> zero >> (n | n))\ndef by5? = (n -> n 5 >> mod >> zero >> (n | n))\ndef fz = by3? >> (drop >> \"f\" | ...) >?> by5? >> (drop >> \"b\" | ...) >!> toStr\n10 >> fz >> print", ["b"], "")
  , ("def by3? = (n -> n 3 >> mod >> zero >> (n | n))\ndef by5? = (n -> n 5 >> mod >> zero >> (n | n))\ndef fz = by3? >> (drop >> \"f\" | ...) >?> by5? >> (drop >> \"b\" | ...) >!> toStr\n7 >> fz >> print", ["7"], "")
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
  , ("def fac = n -> n >> zero? >> ((z -> 1) | (m -> m (m 1 >> - >> fac) >> *)) >> merge\n5 >> fac >> print", ["120"], "")
  , ("def fib = n -> n 2 >> lt? >> ((x y -> x) | (x y -> (x 1 >> - >> fib) >> _ (x 2 >> - >> fib) >> +)) >> merge\n10 >> fib >> print", ["55"], "")
  , ("def pow = b e -> e >> zero? >> ((z -> 1) | (m -> b (b (m 1 >> -) >> pow) >> *)) >> merge\n2 8 >> pow >> print", ["256"], "")
  , ("def fibL = n -> 0 1 n >> [(a b k -> k >> zero? >> ((z -> a >> done) | (m -> b (a b >> +) (m 1 >> -) >> again)) >> merge)] ... >> loop\n20 >> fibL >> print", ["6765"], "")
    -- postfix binder: `x y ->` names the top wires, rest of scope is the
    -- body (same OpenAbs as (x y -> …), now usable bare / as a stage)
  , ("def sq = x -> x x >> *\n5 >> sq >> print", ["25"], "")
  , ("def dst = x1 y1 x2 y2 -> (x2 x1 >> - >> dup >> *) (y2 y1 >> - >> dup >> *) >> +\n0 0 3 4 >> dst >> print", ["25"], "")
    -- mid-pipeline: compute then bind
  , ("def ts =\n dup >> +\n d ->\n d d >> +\n7 >> ts >> print", ["28"], "")
    -- the parenthesized form still works (one code path)
  , ("3 4 >> (x y -> y x >> -) >> print", ["1"], "")
    -- || vertical list literal (a product of lanes) + choose guard fold
  , ("|| [1] || [2] || [3] >> len >> print", ["3"], "")
  , ("([1] [2] [3] >> pack) >> [pass] ... >> map >> len >> print", ["3"], "")
  , ("def sign = || [odd?] [dup >> *] || [negative?] [drop >> 0]\n7 sign >> choose >> (id | 1 ... >> +) >> merge >> print", ["49"], "")
  , ("def sign = ([odd?] [dup >> *] [negative?] [drop >> 0] >> pack2)\n8 sign >> choose >> (id | 1 ... >> +) >> merge >> print", ["9"], "")
  , ("def sign = || [odd?] [dup >> *] || [negative?] [drop >> 0]\n-4 sign >> choose >> (id | 1 ... >> +) >> merge >> print", ["0"], "")
    -- no else lane: none hit -> in2(input)
  , ("5 ([odd?] [dup >> *] >> pack2) >> choose >> (drop >> \"hit\" | drop >> \"miss\") >> merge >> print", ["hit"], "")
  , ("6 ([odd?] [dup >> *] >> pack2) >> choose >> (drop >> \"hit\" | drop >> \"miss\") >> merge >> print", ["miss"], "")
    -- a bound || value reused; and | sum rows still work
  , ("def og = || [odd?] [drop >> \"odd\"]\n3 og >> choose >> (id | drop >> \"even\") >> merge >> print\n4 og >> choose >> (id | drop >> \"even\") >> merge >> print", ["odd", "even"], "")
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
  , ("true false >> and >> print",  ["in2()"], "")
  , ("true true >> and >> print",   ["in1()"], "")
  , ("false true >> or >> print",   ["in1()"], "")
  , ("true true >> xor >> print",   ["in2()"], "")
  , ("true false >> xor >> print",  ["in1()"], "")
  , ("false true >> implies >> print", ["in1()"], "")
  , ("true false >> implies >> print", ["in2()"], "")
  , ("true >> not >> print",        ["in2()"], "")
    -- folding a sum: row of handlers + generated mergeName / foldName
  , ("data Shape = (Int | Int Int | Int Int Int)\ndef rect = in2 >> Shape\n3 4 >> rect >> unShape >> (dup >> * | * | + ... >> +) >> mergeShape >> print", ["12"], "")
  , ("data Shape = (Int | Int Int | Int Int Int)\ndef tri = in3 >> Shape\n1 2 3 >> tri >> [dup >> *] [*] [+ ... >> +] ... >> foldShape >> print", ["6"], "")
    -- multi-wire list literals + matchWith: data-driven first-match guard
  , ("def by3? = (n -> n 3 >> mod >> zero >> (n | n))\n9 [toStr] ([by3?] [drop >> \"fizz\"] >> pack2) >> matchWith >> print", ["fizz"], "")
  , ("def by3? = (n -> n 3 >> mod >> zero >> (n | n))\n7 [toStr] ([by3?] [drop >> \"fizz\"] >> pack2) >> matchWith >> print", ["7"], "")
    -- zip + a fold over flat two-wire elements: the dot product
  , ("(1 2 3 >> pack) (10 20 30 >> pack) >> zip >> [0] [(acc a b -> a b >> * >> acc ... >> +)] ... >> foldList >> print", ["140"], "")
    -- arithmetic completeness + negative literals
  , ("7 3 >> div >> print",  ["2"], "")
  , ("15 3 >> mod >> print", ["0"], "")
  , ("-5 >> print",          ["-5"], "")
  , ("-5 3 >> + >> print",   ["-2"], "")
  , ("5 3 >> gt? >> verdict >> print", ["in1()"], "")
  , ("3 3 >> lte? >> verdict >> print", ["in1()"], "")
    -- prelude round-out
  , ("5 >> range >> print",  ["list(0, 1, 2, 3, 4)"], "")
  , ("5 >> range >> len >> print", ["5"], "")
  , ("5 >> range >> sum >> print", ["10"], "")
  , ("(2 3 4 >> pack) >> product >> print", ["24"], "")
  , ("(1 3 5 >> pack) >> [odd] ... >> map >> all >> print", ["in1()"], "")
  , ("(2 4 >> pack) >> [odd] ... >> map >> any >> print", ["in2()"], "")
  , ("(1 2 3 >> pack) >> [odd?] ... >> map >> partitionSum >> len _ >> print _ >> len >> print", ["2", "1"], "")
  , ("(7 8 >> pack) >> printAll", ["7", "8"], "")
    -- fizzbuzz, the citizenship test
  , ("def fizzbuzz = (n -> (n 15 >> mod >> zero) [\"FizzBuzz\"] [(n 3 >> mod >> zero) [\"Fizz\"] [(n 5 >> mod >> zero) [\"Buzz\"] [n >> toStr] ... >> cond] ... >> cond] ... >> cond)\n15 >> fizzbuzz >> print\n9 >> fizzbuzz >> print\n4 >> fizzbuzz >> print", ["FizzBuzz", "Fizz", "4"], "")
    -- unparse / parse round trip; parse feeds evalCode
  , ("\"dup >> *\" >> parse >> (unparse >> print | print) >> forget", ["dup >> *"], "")
  , ("\"dup >> *\" >> parse >> ((c -> c (6) >> evalCode >> print) | print) >> forget", ["in1(36)"], "")
  , ("\"dup >>\" >> parse >> (forget >> 0 >> print | forget >> 1 >> print) >> forget", ["1"], "")
    -- file IO round trip (railway edges)
  , ("\"/tmp/braid-sprint-test.txt\" \"hi\" >> writeFile >> (\"/tmp/braid-sprint-test.txt\" >> readFile >> (print | print) >> forget | print) >> forget", ["hi"], "")
    -- take / skip
  , ("(1 2 3 4 >> pack) >> 2 _ >> take >> print", ["list(1, 2)"], "")
  , ("(1 2 3 4 >> pack) >> 2 _ >> skip >> print", ["list(3, 4)"], "")
  , (".red >> symStr >> \"k=\" ... >> cat >> print", ["k=red"], "")
    -- Code v1: reflect / sections / evalCode / abstraction elimination
  , ("[dup >> *] >> reflect >> ((c -> c (7) >> evalCode >> print) | print) >> forget", ["in1(49)"], "")
  , ("[dup >> * >> 1 ... >> +] >> reflect >> ((c -> (2 c >> take) (6) >> evalCode >> print) | print) >> forget", ["in1(36)"], "")
  , ("[(x y -> x (2 y >> *) >> +)] >> reflect >> ((c -> c (3) (4) >> evalCode >> print) | print) >> forget", ["in1(11)"], "")
  , ("[(x y -> y)] >> reflect >> ((c -> c (3) (4) >> evalCode >> print) | print) >> forget", ["in1(4)"], "")
    -- the closure gate: (x -> [x]) is a true closure, missed with a message
  , ("[(x -> [x])] >> reflect >> (forget >> 0 >> print | forget >> 1 >> print) >> forget", ["1"], "")
    -- evalCode dynamic check: + on one wire misses, evidence kept
  , ("[+] >> reflect >> ((c -> c (5) >> evalCode >> (forget >> 0 | forget >> 1) >> merge >> print) | forget >> 2 >> print) >> forget", ["1"], "")
    -- GLA: transpose of add is copy; linearity checked over reflected code
  , ("def dualSym = (s -> (s .dup >> equals) [.+] [(s .+ >> equals) [.dup] [s] ... >> cond] ... >> cond)\ndef dualAtom = [(s -> s >> dualSym >> in1 >> Atom)] [(n -> n >> in2 >> Atom)] [(t -> t >> in3 >> Atom)] [(y -> y >> in4 >> Atom)] [(c -> c >> in5 >> Atom)] [(l b -> l b >> in6 >> Atom)] [(c -> c >> in7 >> Atom)] ... >> foldAtom\ndef transposeC = reverse >> [[dualAtom] ... >> map] ... >> map\n[+] >> reflect >> ((c -> (c >> transposeC) (5) >> evalCode >> print) | print) >> forget", ["in1(5, 5)"], "")
    -- matrices as diagrams: composition is matmul ([[1,2],[3,4]] squared)
  , ("def m = (x y -> x (2 y >> *) >> + >> _ ((3 x >> *) (4 y >> *) >> +))\n1 0 >> m >> m >> toStr _ >> _ toStr >> cat >> print", ["715"], "")
    -- split-apply-combine: dup broadcasts, filters split, folds apply
  , ("def sumL = [+] 0 ... >> fold\n(1 2 3 4 >> pack) >> dup >> ([odd?] ... >> filter >> sumL) _ >> _ ([even?] ... >> filter >> sumL) >> + >> print", ["10"], "")
    -- the list monad, all derived in the prelude:
    -- single = return, concat = join, flatMap = bind, filter via bind
  , ("(1 2 3 >> pack) >> reverse >> print", ["list(3, 2, 1)"], "")
  , ("(1 2 >> pack) (3 4 >> pack) >> append >> print", ["list(1, 2, 3, 4)"], "")
  , ("((1 2 >> pack) nil (3 >> pack) >> pack) >> concat >> print", ["list(1, 2, 3)"], "")
  , ("5 >> single >> print", ["list(5)"], "")
  , ("(1 2 3 4 >> pack) >> [odd?] ... >> filter >> print", ["list(1, 3)"], "")
  , ("(1 2 3 >> pack) >> [dup >> _ single >> cons] ... >> flatMap >> print", ["list(1, 1, 2, 2, 3, 3)"], "")
    -- one generic reduction, two Monoid instances (dictionaries as wires)
  , ("(1 2 3 4 >> pack) >> [+] 0 ... >> fold >> print", ["10"], "")
  , ("((1 2 >> pack) (3 >> pack) nil >> pack) >> [append] nil ... >> fold >> print", ["list(1, 2, 3)"], "")
    -- chunked fold + combine = whole fold (associativity licenses
    -- parallel reduce)
  , ("def w = (1 2 3 4 5 6 >> pack) >> [*] 1 ... >> fold\ndef l = (1 2 3 >> pack) >> [*] 1 ... >> fold\ndef r = (4 5 6 >> pack) >> [*] 1 ... >> fold\nw >> _ (l >> _ r >> *) >> eq? >> verdict >> print", ["in1()"], "")
    -- laws as programs, presentations as enumerators
  , ("def xs = (0 1 2 3 >> pack)\nxs >> [(1 ... >> +) >> (2 _ >> *)] ... >> map >> _ (xs >> [(2 _ >> *) >> (1 ... >> +) >> (1 ... >> +)] ... >> map) >> eq? >> verdict >> print", ["in1()"], "")
  , ("def xs = (0 1 2 3 >> pack)\nxs >> [(1 ... >> +) >> (2 _ >> *)] ... >> map >> _ (xs >> [(2 _ >> *) >> (1 ... >> +)] ... >> map) >> eq? >> verdict >> print", ["in2()"], "")
    -- multi-line kleisli: newline absorption around >=> (either side)
  , ("def double2 = 2 _ >> *\ndef process =\n    even?\n    >=> _ 100 >> less?\n    >=> double2 >> ok\n120 >> process >> print", ["in2(120)"], "")
  , ("0 >> (even? >=>\nzero?) >> print", ["in1(0)"], "")
    -- cleanup-baked comparison routers and quoted sections: predicates
    -- built inline, no lambda, no factory
  , ("def equals = eq? >> (_ drop | _ drop)\n5 >> _ 5 >> equals? >> print", ["in1(5)"], "")
  , ("def both = (p q -> [p ... >> apply >> (q ... >> apply | in2) >> merge])\n5 >> ([_ 5 >> equals?] [odd?] >> both) ... >> apply >> print", ["in1(5)"], "")
  , ("def equals = eq? >> (_ drop | _ drop)\ndef both = (p q -> [p ... >> apply >> (q ... >> apply | in2) >> merge])\n6 >> ([_ 5 >> equals?] [odd?] >> both) ... >> apply >> print", ["in2(6)"], "")
  , ("def less = lt? >> (_ drop | _ drop)\ndef whileFn = (p f -> [p ... >> apply >> (f ... >> apply >> again | done) >> merge])\ndef while = whileFn ... >> loop\ndef double = 2 _ >> *\n7 >> [_ 100 >> less?] [double] ... >> while >> print", ["112"], "")
    -- user-built predicates: scaffold-test-cleanup, and factories that
    -- return quoted routers
  , ("def five? = _ 5 >> eq? >> (_ drop | _ drop)\n5 >> five? >> print", ["in1(5)"], "")
  , ("def equalsK = (k -> [_ k >> eq? >> (_ drop | _ drop)])\n7 >> (5 >> equalsK) ... >> apply >> print", ["in2(7)"], "")
  , ("def equalsK = (k -> [_ k >> eq? >> (_ drop | _ drop)])\n5 >> (5 >> equalsK) ... >> apply >> print", ["in1(5)"], "")
  , ("def whileFn = (p f -> [p ... >> apply >> (f ... >> apply >> again | done) >> merge])\ndef while = whileFn ... >> loop\ndef lessThan = (k -> [_ k >> lt? >> (_ drop | _ drop)])\ndef double = 2 _ >> *\n7 >> (100 >> lessThan) [double] ... >> while >> print", ["112"], "")
    -- value-level predicate combinators: negate/both/either on quoted
    -- routers (closures assemble the composed router)
  , ("def negate = (p -> [p ... >> apply >> (in2 | in1) >> merge])\ndef both = (p q -> [p ... >> apply >> (q ... >> apply | in2) >> merge])\ndef either = (p q -> [p ... >> apply >> (in1 | q ... >> apply) >> merge])\ndef small? = _ 10 >> lt? >> (_ drop | _ drop)\n4 >> ([even?] [small?] >> both) ... >> apply >> print", ["in1(4)"], "")
  , ("def negate = (p -> [p ... >> apply >> (in2 | in1) >> merge])\ndef both = (p q -> [p ... >> apply >> (q ... >> apply | in2) >> merge])\ndef either = (p q -> [p ... >> apply >> (in1 | q ... >> apply) >> merge])\ndef small? = _ 10 >> lt? >> (_ drop | _ drop)\n40 >> ([even?] [small?] >> both) ... >> apply >> print", ["in2(40)"], "")
  , ("def negate = (p -> [p ... >> apply >> (in2 | in1) >> merge])\ndef both = (p q -> [p ... >> apply >> (q ... >> apply | in2) >> merge])\ndef either = (p q -> [p ... >> apply >> (in1 | q ... >> apply) >> merge])\ndef small? = _ 10 >> lt? >> (_ drop | _ drop)\n7 >> ([even?] [small?] >> both) ... >> apply >> print", ["in2(7)"], "")
  , ("def negate = (p -> [p ... >> apply >> (in2 | in1) >> merge])\ndef both = (p q -> [p ... >> apply >> (q ... >> apply | in2) >> merge])\ndef either = (p q -> [p ... >> apply >> (in1 | q ... >> apply) >> merge])\ndef small? = _ 10 >> lt? >> (_ drop | _ drop)\n3 >> ([even?] [small?] >> either) ... >> apply >> print", ["in1(3)"], "")
  , ("def negate = (p -> [p ... >> apply >> (in2 | in1) >> merge])\ndef both = (p q -> [p ... >> apply >> (q ... >> apply | in2) >> merge])\ndef either = (p q -> [p ... >> apply >> (in1 | q ... >> apply) >> merge])\ndef small? = _ 10 >> lt? >> (_ drop | _ drop)\n9 >> ([even?] [small?] >> both >> negate) ... >> apply >> print", ["in1(9)"], "")
    -- until = while of the negated predicate, all in-language
  , ("def whileFn = (p f -> [p ... >> apply >> (f ... >> apply >> again | done) >> merge])\ndef while = whileFn ... >> loop\ndef negate = (p -> [p ... >> apply >> (in2 | in1) >> merge])\ndef until = (p f -> (p >> negate) f) ... >> while\ndef big? = _ 100 >> lt? >> (_ drop | _ drop) >> (in2 | in1) >> merge\ndef double = 2 _ >> *\n7 >> [big?] [double] ... >> until >> print", ["112"], "")
    -- router boolean algebra: not = track swap; and/or = one-sided rows
  , ("5 >> odd? >> (in2 | in1) >> merge >> print",  ["in2(5)"], "")
  , ("0 >> even? >> (zero? | in2) >> merge >> print", ["in1(0)"], "")
  , ("6 >> even? >> (zero? | in2) >> merge >> print", ["in2(6)"], "")
  , ("2 >> even? >> (in1 | zero?) >> merge >> print", ["in1(2)"], "")
  , ("7 >> even? >> (in1 | zero?) >> merge >> print", ["in2(7)"], "")
    -- Euclid's subtractive gcd: router negation is a track swap
  , ("def whileFn = (p f -> [p ... >> apply >> (f ... >> apply >> again | done) >> merge])\ndef while = whileFn ... >> loop\ndef not = (in2 | in1) >> merge\ndef neq? = eq? >> not\ndef shrink = lt? >> (swap | ...) >> merge >> _ dup >> - ...\n48 18 >> [neq?] [shrink] ... >> while >> drop ... >> print", ["6"], "")
  , ("def whileFn = (p f -> [p ... >> apply >> (f ... >> apply >> again | done) >> merge])\ndef while = whileFn ... >> loop\ndef not = (in2 | in1) >> merge\ndef neq? = eq? >> not\ndef shrink = lt? >> (swap | ...) >> merge >> _ dup >> - ...\n1071 462 >> [neq?] [shrink] ... >> while >> drop ... >> print", ["21"], "")
    -- recursion: tail recursion replaces the loop harness; tree recursion is new
  , ("def lt100? = _ 100 >> lt? >> (_ drop | _ drop)\ndef double = 2 _ >> *\ndef until100 = lt100? >> (double >> until100 | _) >> merge\n7 >> until100 >> print", ["112"], "")
  , ("def decr = _ 1 >> -\ndef sumTo = (a n -> n >> zero? >> ((z -> a) | (m -> (a m >> +) (m >> decr) >> sumTo)) >> merge)\n0 5 >> sumTo >> print", ["15"], "")
  , ("def decr = _ 1 >> -\ndef lt2? = _ 2 >> lt? >> (_ drop | _ drop)\ndef fib = lt2? >> (_ | (n -> n >> decr >> fib >> _ (n 2 >> - >> fib) >> +)) >> merge\n10 >> fib >> print", ["55"], "")
  , ("5 >> (_ 2 >> -) >> print",           ["3"],  "")
  , ("2 2 >> eq?",                         [],     "in1(2, 2)")
  , ("3 5 >> lt?",                         [],     "in1(3, 5)")
  , ("(1 2 >> pack) >> uncons",               [],     "list(1, 2)")
  , ("nil >> uncons",                   [],     "in1()")
    -- deferred peel builds a nested sum; case(…) folds the whole spine
  , ("def classify = negative? >> (drop >> \"neg\" | pass) >> (pass | zero?) >> case(pass, drop >> \"zero\", toStr)\n-4 >> classify >> print\n0 >> classify >> print\n7 >> classify >> print", ["neg", "zero", "7"], "")
    -- associator round-trip is identity on the routed value
  , ("def tag = negative? >> (drop >> \"neg\" | pass) >> (pass | zero?)\n5 >> tag >> assocL >> assocR >> case(pass, drop >> \"zero\", toStr) >> print", ["5"], "")
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
  , ("5 >> in1\ndup >> * | pass\npass     | 1 ... >> +\nmerge >> print", ["25"], "")
    -- bare rows, line-scoped
  , ("5 >> in1\ndup | +\n+ | id\nmerge >> (x -> x 1 >> +)\nprint",  ["11"], "")
  , ("3 4 >> in2\ndup | +\n+ | id\nmerge >> (x -> x 1 >> +)\nprint", ["8"], "")

    -- match2 as a DERIVED definition (spec: match = row of applies + merge)
  , ("def match2 = (f g s -> s >> (f ... >> apply | g ... >> apply) >> merge)\n5 >> in1 >> [dup >> *] [1 ... >> +] ... >> match2 >> print",
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
  , ("def sign = x -> (x >> negative) [\"neg\"] (x >> zero) [\"zero\"] [x >> toStr] >> firstTrue\n-4 >> sign >> print\n0 >> sign >> print\n7 >> sign >> print", ["neg", "zero", "7"], "")
    -- cut soundness: at stage boundaries, run(prefix) ; run(suffix) =
    -- run(whole) — the concatenative property at spine granularity
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [1 2 >> + >> dup >> *] >> getCode\ndef cutAt =\n    k ->\n    (k c >> take) >> evalCode\n    ((k c >> skip) ... >> evalCode >> (print | forget) >> merge | forget) >> merge\n0 >> cutAt\n1 >> cutAt\n3 >> cutAt", ["9", "9", "9"], "")
    -- vertical cuts: atom slices within a stage are runnable sub-tensors
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef s0 = ([1 2 >> +] >> getCode) >> uncons >> (nil | (s r -> s)) >> merge\n(1 s0 >> take >> single) >> evalCode >> (print | forget) >> merge\n(1 s0 >> skip >> single) >> evalCode >> (print | forget) >> merge", ["1", "2"], "")
    -- box: Code -> Fn without running; the check fires at apply
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\n(2 ([1 2 >> + >> dup >> *] >> getCode) >> take) >> box\napply >> (print | forget) >> merge", ["3"], "")
    -- pack builds the same value as the list(…) literal; pack2 makes
    -- two-wire elements; the empty pack is nil
  , ("def a = 1 (2 (3 nil >> cons) >> cons) >> cons\ndef b = (1 2 3 >> pack)\na >> _ b >> eq? >> verdict >> print", ["in1()"], "")
  , ("(1 2 3 >> pack) >> sum >> print\n(pack) >> len >> print", ["6", "0"], "")
  , ("(1 10 2 20 >> pack2) >> [0] [(acc a b -> (a b >> *) acc >> +)] ... >> foldList >> print", ["50"], "")
  , ("def fanout = [(x -> (x (10 x >> *) >> pack))]\nfanout 7 >> apply >> print", ["list(7, 70)"], "")
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
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [x _ -> x _] >> getCode\n7 8 >> (c) ... >> evalCode >> (print print | forget) >> merge", ["7", "8"], "")
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [x _ -> x x _ >> + _ >> +] >> getCode\n1 2 >> (c) ... >> evalCode >> (print | forget) >> merge", ["4"], "")
  , ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [x _ z -> z _ x] >> getCode\n1 2 3 >> (c) ... >> evalCode >> (print print print | forget) >> merge", ["3", "2", "1"], "")
    -- a `...` binder honestly refuses: its passthrough width is erased
  , ("[x ... -> x ...] >> reflect >> (drop >> \"ok\" | id) >> merge >> print", ["cannot reflect a binder whose parameters end in '...'"], "")
    -- CODATA: an infinite stream, forced one cell at a time. Fn in the
    -- data declaration makes the thunked tail expressible; productive
    -- corecursion (from) is guarded by the quote.
  , ("data Stream(a) = (a Fn⟨• ⇒ Stream(a)⟩)\ndef headS = unStream >> (h t -> h)\ndef tailS = unStream >> (h t -> t) >> apply\ndef from = (n -> n [n 1 >> + >> from] >> Stream)\n0 >> from >> tailS >> tailS >> headS >> print", ["2"], "")
  ]

-- (module source, substring expected in the error)
moduleFailTests :: [(String, String)]
moduleFailTests =
    -- the evalCode arity gap: spliced code produces 2 wires but the
    -- context typed the hit track as 0 (Δ is existential, chosen by the
    -- caller). Used to leak silently (a value on a stack typed empty);
    -- the top-level width backstop now catches it as a clean error,
    -- delivering the guarantee spec-code.md already claimed.
  [ ("def getCode = reflect >> ((c -> c) | drop >> nil) >> merge\ndef c = [1 2] >> getCode\n(c) ... >> evalCode >> (print | forget) >> merge", "result desync")
  , ("def square = dup >> *\ndef square = id\n1", "Duplicate definition")
  , ("def while = drop\ndef while = id\n1",       "Duplicate definition")
  , ("type Bool = (• | •)\ntype Bool = (• | •)\n1", "Duplicate type declaration")
  , ("type Foo = (• | Unknowable)\n1",           "Unknown type name")
  , ("type Bad = (• | Int^n)\n1",                "Exponent variables")
  , ("type Bad = (• | Int^)\n1",                 "Expected an exponent")
  , ("type = (• | •)\n1",                        "Malformed type declaration")
  , ("type Pair(a, b) = (a | Int)\n1",           "must occur in the body")
  , ("data Bad(a, b) = (• | a b)\n1",            "ambiguous product split")
    -- Fn type declarations: missing arrow, unclosed, reserved name
  , ("type Bad(a) = Fn⟨a a⟩\n1",                 "Expected '⇒'")
  , ("type Bad(a) = Fn⟨a ⇒ a\n1",                "close the Fn type")
  , ("type Fn(a) = (• | a)\n1",                  "Malformed type declaration")
  , ("type Bad = Fn\n1",                         "Fn must be written")
    -- a non-final recursive call must report the placement rule, not
    -- panic in appendStack (regression: was a Haskell error)
  , ("def x = x x ... >> +\n1",                  "final atom of its tensor stage")
    -- nominal rigidity: a data type is NOT its unfolding
  , ("type Nat = (• | Nat)\nin1 >> Nat >> unNat >> unNat", "Cannot unify types")
  , ("type dup = (• | dup)\n1",                  "collides")
    -- list elements must be pure pushes (desugar makes it a unify error)
  , ("list(1, 2) >> len >> print",                  "Unclosed group")
  , ("def 5 = id\n1",                             "Malformed definition")
  , ("+",                                         "main requires a nonempty input stack")
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
          where rendered = showArrowA (modAliases m) (normalizeArrow arr)

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
-- the invariant is apply s a == apply s b (the unifier really unified).
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
  ]
  where
    intS = SCons TInt SEnd
    istS = SCons TInt (SCons TStr SEnd)
    ints k = foldr SCons SEnd (replicate k TInt)
    expN nm b = SExp b (Exp 0 (Just (NV nm))) SEnd
    expNr nm b r = SExp b (Exp 0 (Just (NV nm))) r

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
  exNames <- sort . filter (".braid" `isSuffixOf`) <$> listDirectory "examples"
  exFs <- mapM runExample exNames
  let failures = concatMap (maybe [] pure)
        (  map runPass passTests
        ++ map runFail failTests
        ++ map runModuleType moduleTypeTests
        ++ evalFs
        ++ mfailFs
        ++ map runUnif unifTests
        ++ exFs
        )
      total = length passTests + length failTests
            + length moduleTypeTests + length evalTests + length moduleFailTests
            + length unifTests + length exNames
  mapM_ (putStrLn . ("FAIL " ++)) failures
  putStrLn $ show (total - length failures) ++ "/" ++ show total ++ " tests passed"
  if null failures then exitSuccess else exitFailure
