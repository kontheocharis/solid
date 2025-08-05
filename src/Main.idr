-- Entry point for the compiler
module Main

import System
import System.File

import Data.Singleton
import Common
import Utils
import Surface.Presyntax
import Surface.Parsing
import Core.Atoms
import Core.Syntax
import Pipeline.Core
import Pipeline.Compiler
import Control.Monad.State

%default covering

showUsage : IO ()
showUsage = do
  putStrLn "Usage:"
  putStrLn "  solid <filename> [--until <stage>]     Process a source file"
  putStrLn "  solid -e <expr>                        Evaluate an expression"
  putStrLn "  solid -h                               Show this help message"
  putStrLn ""
  putStrLn "Stages:"
  for_ allOptions $ \opt => putStrLn $ "  - " ++ opt
  

main : IO ()
main = do
  args <- getArgs
  run args
  where
    run : List String -> IO ()
    run [_, "-h"] = showUsage
    run [_, filename, "--until", expr] = do
        case fromString expr of
          Just (_ ** _ ** stage) => do
            let (showOutput, compile) = compileUntil (FileInput filename) stage
            result <- compile
            putStrLn $ "Executed until " ++ expr
            putStrLn $ "Result:\n" ++ show @{showOutput} result
          Nothing => do
            putStrLn "Invalid stage name"
            showUsage
            exitWith (ExitFailure 1)
    run [q, filename] = do
      run [q, filename, "--until", "code"]
    run _ = do
      putStrLn "Invalid arguments"
      showUsage
      exitWith (ExitFailure 1)
