-- Test suite: run via `cabal test`.
module Main (main) where

import MiniConcatTypechecker
import Data.List (isInfixOf)
import System.Exit (exitFailure, exitSuccess)

-- (source, expected alpha-normalized type)
passTests :: [(String, String)]
passTests =
  [ -- literals and basic prims
    ("17",            "ρ0 ⇒ Int ρ0")
  , ("1 2",           "ρ0 ⇒ Int Int ρ0")
  , ("1 2 3",         "ρ0 ⇒ Int Int Int ρ0")
  , ("+",             "Int Int ρ0 ⇒ Int ρ0")
  , ("pass",          "ρ0 ⇒ ρ0")

    -- cartesian basis
  , ("swap",          "a0 a1 ρ0 ⇒ a1 a0 ρ0")
  , ("dup",           "a0 ρ0 ⇒ a0 a0 ρ0")
  , ("drop",          "a0 ρ0 ⇒ ρ0")
  , ("id",            "a0 ρ0 ⇒ a0 ρ0")

    -- sequencing and row polymorphism
  , ("1 >> +",        "Int ρ0 ⇒ Int ρ0")
  , ("1 2 >> +",      "ρ0 ⇒ Int ρ0")
  , ("1 2 >> f g >> + >> print", "ρ0 ⇒ ρ0")

    -- newline is strict >>
  , ("1 2\nf g\n+\nprint",       "ρ0 ⇒ ρ0")
  , ("1 2\n\n+",                 "ρ0 ⇒ Int ρ0")   -- blank lines collapse
  , ("1 2 >>\n+",                "ρ0 ⇒ Int ρ0")   -- newline after >> absorbed

    -- worked schemes from the spec (remainder discipline section)
  , ("dup >> *",      "Int ρ0 ⇒ Int ρ0")           -- square
  , ("id drop",       "a0 a1 ρ0 ⇒ a0 ρ0")          -- first
  , ("dup >> id drop","a0 ρ0 ⇒ a0 ρ0")             -- counit law
  , ("dup >> swap",   "a0 ρ0 ⇒ a0 a0 ρ0")          -- commutativity law
  , ("swap >> swap",  "a0 a1 ρ0 ⇒ a0 a1 ρ0")       -- involution

    -- trailing remainder: ... and >>>
  , ("1 2 3 >> f ... >> +",      "ρ0 ⇒ Int Int ρ0")
  , ("1 2 3 >> f >>> +",         "ρ0 ⇒ Int Int ρ0")   -- >>> ≡ the ... form
  , ("1 2 3\nf ...\n+",          "ρ0 ⇒ Int Int ρ0")   -- same, via newlines
  , ("...",                      "ρ0 ⇒ ρ0")           -- bare remainder stage

    -- quotations and apply
  , ("[dup >> *]",               "ρ0 ⇒ Code⟨Int ρ1 ⇒ Int ρ1⟩ ρ0")
  , ("[dup >> *] 7 >> apply",    "ρ0 ⇒ Int ρ0")
  , ("[dup >> *] 7 >> apply >> print", "ρ0 ⇒ ρ0")     -- spec example (49)
  , ("apply",                    "Code⟨ρ0 ⇒ ρ1⟩ ρ0 ⇒ ρ1")

    -- branch and lists
  , ("branch",        "Bool Code⟨ρ0 ⇒ ρ1⟩ Code⟨ρ0 ⇒ ρ1⟩ ρ0 ⇒ ρ1")
  , ("negative?",     "Int ρ0 ⇒ Bool ρ0")
  , ("list(1, 2, 3)", "ρ0 ⇒ List Int ρ0")
  , ("list()",        "ρ0 ⇒ List a0 ρ0")
  , ("map",           "Code⟨a0 ⇒ a1⟩ List a0 ρ0 ⇒ List a1 ρ0")
  , ("fold",          "Code⟨a0 a1 ⇒ a0⟩ a0 List a1 ρ0 ⇒ a0 ρ0")
  ]

-- (source, substring expected in the error)
failTests :: [(String, String)]
failTests =
  [ ("1 true >> +",   "Cannot unify types")
  , ("true >> f",     "Cannot unify types")
    -- Γ inside Code⟨…⟩: binding Γ := Code⟨Γ⇒Δ⟩ ρ must fail the occurs
    -- check now that it traverses element types.
  , ("dup >> apply",  "Occurs check")
  , ("[dup",          "Unclosed quotation")
  , ("]",             "Expected a tensor stage")
    -- branches with different stack effects
  , ("true [1] [drop ...] >> branch", "Occurs check")
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
  [ ("def square = dup >> *\nsquare",           "Int ρ0 ⇒ Int ρ0")
  , ("def square = dup >> *\nsquare >> square", "Int ρ0 ⇒ Int ρ0")
  , ("def first = id drop\n1 2 >> first",       "ρ0 ⇒ Int ρ0")
    -- one def used at two different types = let-polymorphism
  , ("def discard = drop\n1 discard >> true discard", "a0 ρ0 ⇒ Bool ρ0")
  ]

-- (module source, expected print log, expected final stack rendering)
evalTests :: [(String, [String], String)]
evalTests =
  [ ("1 2 >> f g >> + >> print",           ["6"],  "")      -- f=succ, g=double
  , ("1 2 >> swap",                        [],     "2 1")
  , ("1 2 3 >> f ... >> +",                [],     "4 3")
  , ("1 2 3 >> f >>> +",                   [],     "4 3")
  , ("def square = dup >> *\n5 >> square >> print", ["25"], "")
  , ("true false",                         [],     "true false")
  , ("1 2\nswap\nprint\nprint",            ["2", "1"], "")

    -- quotations and apply
  , ("[dup >> *] 7 >> apply >> print",     ["49"], "")   -- from the spec
  , ("[1 2 >> +] >> apply >> print",       ["3"],  "")
  , ("[pass]",                             [],     "[code]")
  , ("def sq = [dup >> *]\nsq 5 >> apply", [],     "25")

    -- branch
  , ("true [1] [2] >> branch >> print",    ["1"],  "")
  , ("false [1] [2] >> branch >> print",   ["2"],  "")
  , ("true [f ...] [g ...] 10 >> branch >> print", ["11"], "")
  , ("5 >> negative?",                     [],     "false")

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
    -- a def's quote closed non-finally (Code⟨•⇒•⟩) meeting an Int wire:
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
