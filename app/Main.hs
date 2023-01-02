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
  import Core.Transformation.ForwardRemover
  import Core.Transformation.ModuleRemover

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
              Right (TypeState c modules _, res') -> do
                res' <- bundle res' modules
                (anfC, res') <- runANF res' 0
                mapM_ print res'
                (interfaces, res') <- runClosureConversion res' c
                res' <- runHoisting res'
                (_, res') <- runANF (reverse interfaces ++ res') anfC
                res'' <- runMono res'
                let res' = nub $ concatMap (`rearrange` res'') res''
                path <- compileModule res' file
                findExecutable "clang" >>= \case
                  Nothing -> putStrLn "Clang not found, skipping compilation"
                  Just clang -> do
                    callCommand $ clang ++ " " ++ path ++ " -w -o " ++ (file -<.> "out")
      _ -> putStrLn "Usage: proton compile <file>"
