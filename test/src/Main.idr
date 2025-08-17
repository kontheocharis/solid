module Main

import System
import System.File
import System.Path
import System.Directory.Tree

%default covering


error : String -> IO a
error e = do
  putStrLn e
  exitWith (ExitFailure 1)

foldersNotFound : IO a
foldersNotFound = error "Did not find test folders cases/fail and cases/pass"

data TestKind : Type where
  Positive : TestKind
  Negative : TestKind

data TestOutput : TestKind -> Type where
  ZeroCode : TestOutput Positive
  ShouldErrorWith : IO String -> TestOutput Negative

record Test (k : TestKind) where
  constructor MkTest
  name : String
  path : Path
  output : TestOutput k
  options : IO String
  source : IO String

record TestRecipe where
  constructor MkTestRecipe
  root : Path
  toPass : List (Test Positive)
  toFail : List (Test Negative)
  
parseTestSource : {k : _} -> Path -> String -> Test k
parseTestSource p str = ?parseTestSource_rhs

runTest : {k : _} -> Test k -> IO ()
runTest (MkTest name path ZeroCode options source) = ?fjJ_1
runTest (MkTest name path (ShouldErrorWith errM) options source) = ?fjJ_2

runTests : TestRecipe -> IO ()
runTests (MkTestRecipe root toPass toFail) = for_ toFail runTest >> for_ toPass runTest

gatherTests : {k : _} -> {p : _} -> Tree p -> IO (List (Test k))
gatherTests (MkTree files rest) = do
  theseTests <- for files $ \file => do
    contents <- readFile (fileName file)
    case contents of
      Left err => error (show err)
      Right contents => pure $ parseTestSource {k} p contents
  restTests <- for rest $ \(otherName ** otherTreeM) => do
    other <- otherTreeM
    gatherTests {k} other
  pure $ theseTests ++ join restTests

formRecipe : {p : _} -> Tree p -> IO TestRecipe
formRecipe t = case (sort t) of
  MkTree _ [(casesName ** casesTree)] => case (fileName casesName) of
    "cases" => casesTree >>= formRecipe
    _ => foldersNotFound
  MkTree _ [(failName ** failTreeM), (passName ** passTreeM)] =>
    case (fileName failName, fileName passName) of
      ("fail", "pass") => do
        failTree <- failTreeM >>= gatherTests
        passTree <- passTreeM >>= gatherTests
        pure $ MkTestRecipe p failTree passTree
      _ => foldersNotFound
  _ => foldersNotFound
  
describeRecipe : TestRecipe -> IO ()
describeRecipe (MkTestRecipe root fail succ) = do
  putStrLn "Test location: \{show root}"
  putStrLn "Running \{show $ length fail} negative tests and \{show $ length succ} positive tests..."

showUsage : IO ()
showUsage = do
  putStrLn "Usage:"
  putStrLn "  tests <path>    Run the tests under the given path"
  
main : IO ()
main = do
  args <- getArgs
  run args
  where
    run : List String -> IO ()
    run [_, path] = do
      tree <- explore (parse path)
      recipe <- formRecipe tree
      describeRecipe recipe
      runTests recipe
    run _ = do
      putStrLn "Invalid arguments"
      showUsage
      exitWith (ExitFailure 1)

    
 