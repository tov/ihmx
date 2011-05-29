module Main where

import Control.Applicative
import System.Console.Editline.Readline
import Text.ParserCombinators.Parsec
import IO

import Infer
import Parsable

main = do
  initialize
  repl

repl = do
  mline <- readline "> "
  case mline of
    Nothing   -> return ()
    Just line -> do
      addHistory line
      case runParser (genParser <* eof) [] "" line of
        Left err  -> hPutStrLn stderr (show err)
        Right exp -> case showInfer exp of
          Left err    -> hPutStrLn stderr err
          Right (t,c) ->
            putStrLn $ show t ++ if null c then "" else " constraint " ++ c
      repl
