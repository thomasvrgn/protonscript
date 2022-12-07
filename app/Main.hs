{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE LambdaCase #-}
module Main where
  import Core.Parser.Parser (parseProton)
  import Core.Checker.Checker (runInfer)
  import Core.Error (printError, printParseError)
  import Core.Transformation.ANF
  import Core.Transformation.Monomorphization (runMono)
  import Core.Compiler.Compiler
  import Core.Compiler.Generation
  import System.Process.Extra
  import System.Directory.Extra
  import System.Environment
  import System.FilePath

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
            res <- runInfer ast'
            case res of
              Left err -> printError err "While typechecking the program"
              Right (_, res') -> do
                res' <- runANF res'
                res' <- runMono res'
                (decls, cAST) <- compile res'
                let output = concatMap generateToplevel cAST
                let outputFile = file -<.> "c"
                let executable = file -<.> "out"
                findExecutable "clang" >>= \case
                  Nothing -> putStrLn "Clang not found, skipping compilation"
                  Just clang -> do
                    writeFile outputFile ("#include <stdio.h>\n" ++ concat (reverse decls) ++ output)
                    callCommand $ clang ++ " " ++ outputFile ++ " -w -o " ++ executable
                    removeFile outputFile
      _ -> putStrLn "Usage: proton compile <file>"
