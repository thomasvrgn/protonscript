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

  main :: IO ()
  main = do
    let file = "example/index.ts"
    x <- readFile file
    let ast = parseProton file x
    case ast of
      Left err -> printParseError err file
      Right ast' -> do
        res <- runInfer ast'
        case res of
          Left err -> printError err "While typechecking the program"
          Right (_, res') -> do
            mapM_ print res'

            res' <- runANF res'
            res' <- runMono res'

            (decls, cAST) <- compile res'
            let output = concatMap generateToplevel cAST
            findExecutable "clang" >>= \case
              Nothing -> putStrLn "Clang not found, skipping compilation"
              Just clang -> do
                writeFile "example/index.c" ("#include <stdio.h>\n" ++ concat (reverse decls) ++ output)
                callCommand $ clang ++ " example/index.c -w -o example/index.out"
                -- removeFile "example/index.c"
