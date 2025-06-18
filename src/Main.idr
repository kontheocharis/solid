-- Entry point for the compiler
module Main

import System
import System.File

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
  putStrLn "  compiler <filename> [--until <stage>]     Process a source file"
  putStrLn "  compiler -e <expr>                        Evaluate an expression"
  putStrLn "  compiler -h                               Show this help message"
  putStrLn ""
  putStrLn "Stages:"
  for_ allOptions \opt => putStrLn $ "  - " ++ opt
  

main : IO ()
main = do
  args <- getArgs
  case args of
    [_, "-h"] => showUsage
    [_, filename, "--until", expr] => do
      case fromString expr of
        Just (_ ** _ ** stage) => do
          result <- compileUntil (FileInput filename) stage
          putStrLn $ "Executed until " ++ expr
        Nothing => do
          putStrLn "Invalid stage name"
          showUsage
          exitWith (ExitFailure 1)
    [_, filename] => do
      result <- compileUntil (FileInput filename) (get Code)
      putStrLn $ "Done"
    _ => do
      putStrLn "Invalid arguments"
      showUsage
      exitWith (ExitFailure 1)
