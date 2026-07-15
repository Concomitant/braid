module Main where

import MiniConcatTypechecker

main :: IO ()
main = do
  putStrLn $ "program: " ++ exampleSrc
  case checkModule exampleSrc of
    Left err -> putStrLn $ "Type error: " ++ err
    Right m -> do
      case modMain m of
        Just (_, arr) -> putStrLn $ "type:    " ++ show arr
        Nothing       -> putStrLn "no main program"
      case runModule exampleSrc of
        Left err -> putStrLn $ "Runtime error: " ++ err
        Right (stack, logs) -> do
          mapM_ (putStrLn . ("output:  " ++)) logs
          putStrLn $ "stack:   "
            ++ if null stack then "•" else unwords (map show stack)
