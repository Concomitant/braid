-- Test suite: run via `cabal test`.
module Main (main) where

import MiniConcatTypechecker
import Data.List (isInfixOf)
import System.Exit (exitFailure, exitSuccess)

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
  , ("1 2 >> f g >> + >> print", "• ⇒ •")

    -- newline is strict >>
  , ("1 2\nf g\n+\nprint",       "• ⇒ •")
  , ("1 2\n\n+",                 "• ⇒ Int")   -- blank lines collapse
  , ("1 2 >>\n+",                "• ⇒ Int")   -- newline after >> absorbed

    -- worked schemes from the spec (now exact, matching it verbatim)
  , ("dup >> *",      "Int ⇒ Int")           -- square
  , ("id drop",       "a0 a1 ⇒ a0")          -- first
  , ("dup >> id drop","a0 ⇒ a0")             -- counit law
  , ("dup >> swap",   "a0 ⇒ a0 a0")          -- commutativity law
  , ("swap >> swap",  "a0 a1 ⇒ a0 a1")       -- involution

    -- trailing remainder: ... and >>> (ops are exact, so deep stacks need it too)
  , ("1 2 3 >> f ... >> + ...",  "• ⇒ Int Int")
  , ("1 2 3 >> f >>> + ...",     "• ⇒ Int Int")   -- >>> ≡ the ... form
  , ("1 2 3\nf ...\n+ ...",      "• ⇒ Int Int")   -- same, via newlines
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
  , ("(1 ... >> +) f",   "Int Int ⇒ Int Int")  -- compound closed non-finally
  , ("f (1 ... >> +)",   "Int Int ⇒ Int Int")  -- compound open finally
  , ("(pass >> drop) f", "a0 Int ⇒ Int")       -- linked tails close soundly

    -- named open abstractions (spec examples, exact types)
  , ("(x -> x)",              "a0 ⇒ a0")
  , ("(x y -> x)",            "a0 a1 ⇒ a0")        -- projection ≡ id drop
  , ("(x y -> y x)",          "a0 a1 ⇒ a1 a0")     -- ≡ swap
  , ("(x -> x x >> *)",       "Int ⇒ Int")          -- named square ≡ dup >> *
  , ("(x -> x 1 >> +)",       "Int ⇒ Int")          -- named increment
  , ("(x y -> x y >> +)",     "Int Int ⇒ Int")
  , ("(x y -> x x >> * >> y ... >> +)", "Int Int ⇒ Int")  -- reuse + reorder
  , ("(f -> f)",              "a0 ⇒ a0")            -- parameters shadow globals
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
    -- bare rows: each LINE is a code row (>> binds tighter than |,
    -- | tighter than newline)
  , ("dup | +",                  "(a0 | Int Int) ⇒ (a0 a0 | Int)")
  , ("dup | +\n+ | id\nmerge",   "(Int | Int Int) ⇒ Int")
  , ("1 ... >> + | ...",         "(Int | σ0) ⇒ (Int | σ0)")

    -- routers: predicates keep and route their input (hit = track 1)
  , ("negative?",     "Int ⇒ (Int | Int)")
  , ("odd?",          "Int ⇒ (Int | Int)")
  , ("zero?",         "Int ⇒ (Int | Int)")
  , ("eq?",           "a0 a0 ⇒ (a0 a0 | a0 a0)")
  , ("lt?",           "Int Int ⇒ (Int Int | Int Int)")
  , ("-",             "Int Int ⇒ Int")
  , ("uncons",        "List a0 ⇒ (• | a0 List a0)")
    -- the guard machine
  , ("if",            "ρ0 ⇒ (ρ1 | ρ0)")
  , ("otherwise",     "ρ0 ⇒ (ρ0 | ())")
  , ("elif",          "(ρ0 | Fn⟨ρ1 ⇒ ρ0⟩ (ρ1 | ρ2)) ⇒ (ρ0 | ρ2)")
  , ("endif",         "(ρ0 | Fn⟨ρ1 ⇒ ρ0⟩ (ρ1 | ())) ⇒ ρ0")
  , ("loop",          "Fn⟨ρ0 ⇒ (ρ0 | ρ1)⟩ ρ0 ⇒ ρ1")
    -- loop protocol aliases: again ≡ in1 (continue), done ≡ in2 (exit)
  , ("again",         "ρ0 ⇒ (ρ0 | σ0)")
  , ("done",          "ρ0 ⇒ (ρ1 | ρ0 | σ0)")
  , ("7 >> if\n... | [dup >> *] odd?\nelif\n... | [1 ... >> +] otherwise\nendif", "• ⇒ Int")
    -- lists
  , ("list(1, 2, 3)", "• ⇒ List Int")
  , ("list()",        "• ⇒ List a0")
  , ("map",           "Fn⟨a0 ⇒ a1⟩ List a0 ⇒ List a1")
  , ("fold",          "Fn⟨a0 a1 ⇒ a0⟩ a0 List a1 ⇒ a0")
  ]

-- (source, substring expected in the error)
failTests :: [(String, String)]
failTests =
  [ ("1 true >> +",   "Cannot unify types")
  , ("true >> f",     "Cannot unify types")
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
    -- a guard chain without its otherwise-clause: endif demands the
    -- uninhabited miss track, so the missing else is a TYPE error
  , ("7 >> if\n... | [dup >> *] odd?\nendif", "Cannot unify types")
    -- list elements must be pure pushes
  , ("list(drop)",    "Cannot unify stacks")
  , ("list(1 2",      "Expected ',' or ')'")
  , ("f ... g",       "'...' must be the final atom")
  , ("1 >",           "Unexpected '>'")
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
  ]

-- (module source, expected alpha-normalized type of main)
moduleTypeTests :: [(String, String)]
moduleTypeTests =
  [ ("def square = dup >> *\nsquare",           "Int ⇒ Int")
    -- >=> is Kleisli composition in the sum monad
  , ("even? >=> zero?",                         "Int ⇒ (Int | Int)")
  , ("def square = dup >> *\nsquare >> square", "Int ⇒ Int")
  , ("def first = id drop\n1 2 >> first",       "• ⇒ Int")
    -- one def used at two different types = let-polymorphism
  , ("def discard = drop\n1 discard >> true discard", "a0 ⇒ (• | •)")
    -- recursive defs (monomorphic self-reference)
  , ("def decr = _ 1 >> -\ndef lt2? = _ 2 >> lt? >> (_ drop | _ drop)\ndef fib = lt2? >> (_ | (n -> n >> decr >> fib >> _ (n 2 >> - >> fib) >> +)) >> merge\nfib", "Int ⇒ Int")
  ]

-- (module source, expected print log, expected final stack rendering)
evalTests :: [(String, [String], String)]
evalTests =
  [ ("1 2 >> f g >> + >> print",           ["6"],  "")      -- f=succ, g=double
  , ("1 2 >> swap",                        [],     "2 1")
  , ("1 2 3 >> f ... >> + ...",            [],     "4 3")
  , ("1 2 3 >> f >>> + ...",               [],     "4 3")
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
  , ("5 8 >> (1 ... >> +) f >> + >> print", ["15"], "")

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
    -- the if/elif/otherwise/endif idiom
  , ("7 >> if\n... | [dup >> *] odd?\nelif\n... | [drop >> 0] negative?\nelif\n... | [1 ... >> +] otherwise\nendif\nprint", ["49"], "")
  , ("8 >> if\n... | [dup >> *] odd?\nelif\n... | [drop >> 0] negative?\nelif\n... | [1 ... >> +] otherwise\nendif\nprint", ["9"], "")
    -- loop: Elgot iteration (sum 1..5)
  , ("def decr = (x -> x 1 >> -)\ndef sumStep = (a n -> n >> zero? >> ((z -> a >> done) | (m -> (a m >> +) (m >> decr) >> again)) >> merge)\n0 5 >> [sumStep] ... >> loop >> print", ["15"], "")
    -- the guard machine as a loop body
  , ("0 3 >> [(a n -> n >> if\n... | [(z -> a >> done)] zero?\nelif\n... | [(m -> (a m >> +) (m 1 >> -) >> again)] otherwise\nendif)] ... >> loop >> print", ["6"], "")
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
    -- prelude defs available with no local definition
  , ("5 >> _ 5 >> equals >> print",             ["in1(5)"], "")
  , ("def double = 2 _ >> *\n7 >> [_ 100 >> less] [double] ... >> while >> print", ["112"], "")
  , ("7 >> [_ 100 >> less >> not] [dup >> +] ... >> until >> print", ["112"], "")
    -- user defs shadow prelude defs
  , ("def while = drop\n1 2 >> while ... >> print", ["2"], "")
    -- >=>: short-circuiting Kleisli chains; in1 lifts pure stages
  , ("4 >> (even? >=> zero?) >> print",         ["in2(4)"], "")
  , ("0 >> (even? >=> zero?) >> print",         ["in1(0)"], "")
  , ("7 >> (even? >=> zero?) >> print",         ["in2(7)"], "")
  , ("def double = 2 _ >> *\n4 >> (even? >=> _ 100 >> less >=> double >> in1) >> print", ["in1(8)"], "")
  , ("def double = 2 _ >> *\n120 >> (even? >=> _ 100 >> less >=> double >> in1) >> print", ["in2(120)"], "")
  , ("def double = 2 _ >> *\n7 >> (even? >=> _ 100 >> less >=> double >> in1) >> print", ["in2(7)"], "")
  , ("5 >> (_ 5 >> equals >=> odd?) >> print",  ["in1(5)"], "")
    -- cleanup-baked comparison routers and quoted sections: predicates
    -- built inline, no lambda, no factory
  , ("def equals = eq? >> (_ drop | _ drop)\n5 >> _ 5 >> equals >> print", ["in1(5)"], "")
  , ("def equals = eq? >> (_ drop | _ drop)\ndef both = (p q -> [p ... >> apply >> (q ... >> apply | in2) >> merge])\n5 >> ([_ 5 >> equals] [odd?] >> both) ... >> apply >> print", ["in1(5)"], "")
  , ("def equals = eq? >> (_ drop | _ drop)\ndef both = (p q -> [p ... >> apply >> (q ... >> apply | in2) >> merge])\n6 >> ([_ 5 >> equals] [odd?] >> both) ... >> apply >> print", ["in2(6)"], "")
  , ("def less = lt? >> (_ drop | _ drop)\ndef whileFn = (p f -> [p ... >> apply >> (f ... >> apply >> again | done) >> merge])\ndef while = whileFn ... >> loop\ndef double = 2 _ >> *\n7 >> [_ 100 >> less] [double] ... >> while >> print", ["112"], "")
    -- user-built predicates: scaffold-test-cleanup, and factories that
    -- return quoted routers
  , ("def five? = _ 5 >> eq? >> (_ drop | _ drop)\n5 >> five? >> print", ["in1(5)"], "")
  , ("def equals = (k -> [_ k >> eq? >> (_ drop | _ drop)])\n7 >> (5 >> equals) ... >> apply >> print", ["in2(7)"], "")
  , ("def equals = (k -> [_ k >> eq? >> (_ drop | _ drop)])\n5 >> (5 >> equals) ... >> apply >> print", ["in1(5)"], "")
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
  , ("list(1, 2) >> uncons",               [],     "in2(1, list(2))")
  , ("list() >> uncons",                   [],     "in1()")
    -- multi-line rows: newlines adjacent to | are absorbed (both styles)
  , ("5 >> in1\ndup >> * |\n1 ... >> +\nmerge >> print", ["25"], "")
    -- bare rows, line-scoped
  , ("5 >> in1\ndup | +\n+ | id\nmerge >> (x -> x 1 >> +)\nprint",  ["11"], "")
  , ("3 4 >> in2\ndup | +\n+ | id\nmerge >> (x -> x 1 >> +)\nprint", ["8"], "")

    -- match2 as a DERIVED definition (spec: match = row of applies + merge)
  , ("def match2 = (f g s -> s >> (f ... >> apply | g ... >> apply) >> merge)\n5 >> in1 >> [dup >> *] [1 ... >> +] ... >> match2 >> print",
                                           ["25"], "")

    -- lists: the spec's sum-of-squares program
  , ("list(1, 2, 3)",                      [],     "list(1, 2, 3)")
  , ("[dup >> *] list(1, 2, 3, 4, 5)\nmap\n[+] 0 id\nfold\nprint",
                                           ["55"], "")
  ]

-- (module source, substring expected in the error)
moduleFailTests :: [(String, String)]
moduleFailTests =
  [ ("def square = dup >> *\ndef square = id\n1", "Duplicate definition")
  , ("def while = drop\ndef while = id\n1",       "Duplicate definition")
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
          | show (normalizeArrow arr) == expected -> Nothing
          | otherwise ->
              Just $ show src ++ ": expected " ++ expected
                   ++ ", got " ++ show (normalizeArrow arr)

runEval :: (String, [String], String) -> Maybe String
runEval (src, wantLog, wantStack) =
  case runModule src of
    Left err -> Just $ show src ++ ": runtime/type error: " ++ err
    Right (stack, logs)
      | logs == wantLog && unwords (map show stack) == wantStack -> Nothing
      | otherwise ->
          Just $ show src ++ ": expected log " ++ show wantLog
               ++ " stack " ++ show wantStack
               ++ ", got log " ++ show logs
               ++ " stack " ++ show (unwords (map show stack))

runModuleFail :: (String, String) -> Maybe String
runModuleFail (src, fragment) =
  case runModule src of
    Right (stack, logs) ->
      Just $ show src ++ ": expected failure containing " ++ show fragment
           ++ ", but ran with stack " ++ show (unwords (map show stack))
           ++ " log " ++ show logs
    Left err
      | fragment `isInfixOf` err -> Nothing
      | otherwise ->
          Just $ show src ++ ": expected error containing " ++ show fragment
               ++ ", got: " ++ err

main :: IO ()
main = do
  let failures = concatMap (maybe [] pure)
        (  map runPass passTests
        ++ map runFail failTests
        ++ map runModuleType moduleTypeTests
        ++ map runEval evalTests
        ++ map runModuleFail moduleFailTests
        )
      total = length passTests + length failTests
            + length moduleTypeTests + length evalTests + length moduleFailTests
  mapM_ (putStrLn . ("FAIL " ++)) failures
  putStrLn $ show (total - length failures) ++ "/" ++ show total ++ " tests passed"
  if null failures then exitSuccess else exitFailure
