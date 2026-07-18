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

    -- branch and lists
  , ("branch",        "Bool Fn⟨ρ0 ⇒ ρ1⟩ Fn⟨ρ0 ⇒ ρ1⟩ ρ0 ⇒ ρ1")
  , ("negative?",     "Int ⇒ Bool")
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
    -- branches with different stack effects ([1] : Fn⟨• ⇒ Int⟩ forces Γ := •)
  , ("true [1] [drop ...] >> branch", "Cannot unify stacks")
    -- list elements must be pure pushes
  , ("list(drop)",    "Cannot unify stacks")
  , ("list(1 2",      "Expected ',' or ')'")
  , ("f ... g",       "'...' must be the final atom")
  , ("1 >",           "Unexpected '>'")
  , ("nonsense42x",   "Unknown primitive")
  , ("",              "Expected a tensor stage")
  ]

-- (module source, expected alpha-normalized type of main)
moduleTypeTests :: [(String, String)]
moduleTypeTests =
  [ ("def square = dup >> *\nsquare",           "Int ⇒ Int")
  , ("def square = dup >> *\nsquare >> square", "Int ⇒ Int")
  , ("def first = id drop\n1 2 >> first",       "• ⇒ Int")
    -- one def used at two different types = let-polymorphism
  , ("def discard = drop\n1 discard >> true discard", "a0 ⇒ Bool")
  ]

-- (module source, expected print log, expected final stack rendering)
evalTests :: [(String, [String], String)]
evalTests =
  [ ("1 2 >> f g >> + >> print",           ["6"],  "")      -- f=succ, g=double
  , ("1 2 >> swap",                        [],     "2 1")
  , ("1 2 3 >> f ... >> + ...",            [],     "4 3")
  , ("1 2 3 >> f >>> + ...",               [],     "4 3")
  , ("def square = dup >> *\n5 >> square >> print", ["25"], "")
  , ("true false",                         [],     "true false")
  , ("1 2\nswap\nprint ...\nprint",        ["2", "1"], "")
  , ("1\n2 id",                            [],     "2 1")
  , ("1\n2 ...",                           [],     "2 1")

    -- quotations and apply
  , ("[dup >> *] 7 >> apply >> print",     ["49"], "")   -- from the spec
  , ("[1 2 >> +] >> apply >> print",       ["3"],  "")
  , ("[pass]",                             [],     "[fn]")
  , ("def sq = [dup >> *]\nsq 5 >> apply", [],     "25")

    -- branch
  , ("true [1] [2] >> branch >> print",    ["1"],  "")
  , ("false [1] [2] >> branch >> print",   ["2"],  "")
  , ("true [f ...] [g ...] 10 >> branch >> print", ["11"], "")
  , ("5 >> negative?",                     [],     "false")

    -- grouping
  , ("7 >> (dup >> *) >> print",           ["49"], "")
  , ("5 8 >> (1 ... >> +) f >> + >> print", ["15"], "")

    -- lists: the spec's sum-of-squares program
  , ("list(1, 2, 3)",                      [],     "list(1, 2, 3)")
  , ("[dup >> *] list(1, 2, 3, 4, 5)\nmap\n[+] 0 id\nfold\nprint",
                                           ["55"], "")
  ]

-- (module source, substring expected in the error)
moduleFailTests :: [(String, String)]
moduleFailTests =
  [ ("def square = dup >> *\ndef square = id\n1", "Duplicate definition")
  , ("def 5 = id\n1",                             "Malformed definition")
  , ("+",                                         "main requires a nonempty input stack")
    -- a def's quote closed non-finally (Fn⟨•⇒•⟩) meeting an Int wire:
    -- the once-unreachable closed-stack mismatch, now real
  , ("def q = [pass]\nq 1 >> apply",              "Cannot unify stacks")
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
