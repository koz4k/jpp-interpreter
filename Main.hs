module Main where


import Lexer
import Parser
import Layout
import StaticCheck
import Interpreter

import Control.Monad.Except

import System.Environment ( getArgs )
import System.Exit ( exitFailure, exitSuccess )
import System.IO (hPutStrLn, stderr)


myLLexer :: String -> [Token]
myLLexer = resolveLayout True . myLexer

runFile :: FilePath -> IO ()
runFile f = readFile f >>= run

run :: String -> IO ()
run s = let ts = myLLexer s in
          case runExcept $ handleAll ts of
            Right out -> do
              putStr out
              exitSuccess
            Left e -> do
              hPutStrLn stderr e
              exitFailure
  where
    handleAll ts = do
      prog <- handleParse ts
      handleStaticCheck prog
      handleInterpret prog
    handleParse ts = pProgram ts `catchError`
      (throwError . ("parse error: " ++))
    handleStaticCheck prog = staticCheck prog `catchError`
      (throwError . ("static check error: " ++))
    handleInterpret prog = interpret prog `catchError`
      (throwError . ("runtime error: " ++))

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Intepret a program from stdin."
    , "  (file)          Intepret a program from the given file."
    ]
  exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    [] -> getContents >>= run
    [file] -> runFile file
    _ -> usage
