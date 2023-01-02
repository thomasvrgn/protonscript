module Core.Transformation.ForwardRemover where
  import Core.Parser.AST.Expression
  import Core.Parser.AST.Literal
  import Core.Checker.Definition.Type
  import Data.Maybe

  findStructure :: String -> [Located (Toplevel Type)] -> Maybe (Located (Toplevel Type))
  findStructure name (x@(TStructure _ name' _ :>: _):xs) = if name == name' then Just x else findStructure name xs
  findStructure name (_:xs) = findStructure name xs
  findStructure _ [] = Nothing

  findNames :: Type -> [String]
  findNames (TApp t x) = findNames t ++ findNames x
  findNames (TPtr t) = findNames t
  findNames (TId n) = [n]
  findNames _ = []
   
  rearrange :: Located (Toplevel Type) -> [Located (Toplevel Type)] -> [Located (Toplevel Type)]
  rearrange z@(TStructure _ name fields :>: _) xs = do
    let x = catMaybes $ concatMap (\(_ :@ t) -> do
              let names = filter ((/= name)) $ findNames t
              map (\n -> rearrange <$> (findStructure n xs) <*> pure xs) names) fields
    concat x ++ [z]
  rearrange x _ = [x]
  