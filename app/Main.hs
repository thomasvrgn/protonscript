{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
module Main where
  import Core.Parser.Parser (parseProton)
  import Core.Checker.Checker (runInfer)
  import Core.Error (printError, printParseError)
  import Core.Transformation.ANF
  import Core.Transformation.ClosureConversion
  import Core.Transformation.Monomorphization (runMono)
  import Core.Transformation.Hoisting
  import Core.Compiler.Compiler
  import Core.Compiler.Generation
  import System.Process.Extra
  import System.Directory.Extra
  import System.Environment
  import System.FilePath
  import Core.Checker.Unification
  import Core.Checker.Definition.Type
  import Core.Parser.AST.Literal
  import Core.Parser.AST.Expression
  import Data.List
  import qualified Data.Map as M

  compileModule :: [Located (Toplevel Type)] -> String -> IO String
  compileModule xs path = do
    (decls, cAST) <- compile xs
    let output = concatMap generateToplevel cAST
    let outputFile = path -<.> "c"
    writeFile outputFile ("#include <stdio.h>\n" ++ concat (reverse decls) ++ output)
    return outputFile

  main :: IO ()
  main = do
    args <- getArgs
    case args of
      ("compile":file:_) -> do
        x <- readFile file
        let ast = parseProton file x
        case ast of
          Left err -> printParseError err file
          Right ast' -> do
            res <- runInfer (takeDirectory file, True) ast'
            case res of
              Left err -> printError err "While typechecking the program"
              Right (TypeState _ modules _, res') -> do
                res' <- runANF $ res'
                res' <- runMono res'
                path <- compileModule res' file
                mods <- M.elems <$> mapM (\(Module path mod) -> compileModule mod path) modules
                print mods
                findExecutable "clang" >>= \case
                  Nothing -> putStrLn "Clang not found, skipping compilation"
                  Just clang -> do
                    callCommand $ clang ++ " " ++ path ++ " " ++ intercalate " " mods ++ " -w -o " ++ (file -<.> "out")
      _ -> putStrLn "Usage: proton compile <file>"
