module Main

import System
import System.File

import Common
import Utils
import Surface.Presyntax
import Surface.Parsing

%default covering

processProgram : String -> IO ()
processProgram s = do
  Right parsed <- pure $ parse topLevelBlock s
    | Left err => do
        putStrLn "Parse error:"
        putStrLn $ "  " ++ show err
        exitWith (ExitFailure 1)
  -- (Evidence _ sig) <- evalStateT dummyLoc $ elabSig parsed
  putStrLn $ "-- Raw program:\n" ++ show parsed
  -- putStrLn $ "-- Checked program:\n" ++ show sig

-- evalTerm : (bs : Names) => Context gs ns bs -> String -> IO ()
-- evalTerm ctx s = do
--   Right parsed <- pure $ parse tm s
--     | Left err => do
--         putStrLn "Parse error:"
--         putStrLn $ "  " ++ show err
--         exitWith (ExitFailure 1)
--   (tm, ty) <- evalStateT dummyLoc $ infer (elab Infer parsed) ctx
--   let val = eval ctx.globEnv ctx.local.env tm
--   putStrLn $ "Raw: " ++ show parsed
--   putStrLn $ "Type: " ++ show ty
--   putStrLn $ "Value: " ++ show val

-- processTerm : String -> IO ()
-- processTerm input = evalTerm (MkContext [<] [<]) input

processFile : String -> IO ()
processFile filename = do
  Right content <- readFile filename
    | Left err => do
        putStrLn $ "Error reading file: " ++ show err
        exitWith (ExitFailure 1)
  processProgram content

showUsage : IO ()
showUsage = do
  putStrLn "Usage:"
  putStrLn "  compiler <filename>     Process a source file"
  putStrLn "  compiler -e <expr>      Evaluate an expression"
  putStrLn "  compiler -h             Show this help message"

main : IO ()
main = do
  args <- getArgs
  case args of
    [_, "-h"] => showUsage
    -- [_, "-e", expr] => processTerm expr
    [_, filename] => processFile filename
    _ => do
      putStrLn "Invalid arguments"
      showUsage
      exitWith (ExitFailure 1)
