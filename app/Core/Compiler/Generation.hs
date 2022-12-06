module Core.Compiler.Generation where
  import Core.Parser.AST.Expression
  import Core.Parser.AST.Literal
  import Control.Arrow
  import Core.Compiler.Compiler
  import Data.List

  generateToplevel :: Located (Toplevel CType) -> String
  generateToplevel (TFunction _ ret name args body :>: _)
    = ret ++ " " ++ name ++ "(" ++ intercalate ", " (map (\(n :@ t) -> t ++ " " ++ n) args) ++ ") {\n" ++ concatMap generateStatement body ++ "}"
  generateToplevel (TAssignment (name :@ ret) expr :>: _) 
    = ret ++ " " ++ name ++ " = " ++ generateExpression expr ++ ";"
  generateToplevel (TConstant (name :@ ret) expr :>: _)
    = "const " ++ ret ++ " " ++ name ++ " = " ++ generateExpression expr ++ ";"
  generateToplevel (TEnumeration n fields :>: _)
    = "enum " ++ n ++ " {\n" ++ concatMap (\v -> v ++ ",\n") fields ++ "};"
  generateToplevel (TStructure _ name fields :>: _)
    = "struct " ++ name ++ " {\n" ++ concatMap (\(n :@ t) -> t ++ " " ++ n ++ ";\n") fields ++ "};"
  generateToplevel (TDeclaration (name :@ ret) :>: _)
    = "extern " ++ ret ++ " " ++ name ++ ";"
  generateToplevel (TDeclarationFunction (name :@ ret) args :>: _)
    = "extern " ++ ret ++ " " ++ name ++ "(" ++ intercalate ", " args ++ ");"
  generateToplevel _ = error "not supported yet"

  generateStatement :: Located (Statement CType) -> String
  generateStatement (SAssignment (name :@ ret) expr :>: _) = do
    ret ++ " " ++ name ++ " = " ++ generateExpression expr ++ ";"
  generateStatement (SIf cond then' else' :>: _) = do
    let cond' = generateExpression cond
    let then'' = generateExpression then'
    let else'' = generateExpression <$> else'
    "if (" ++ cond' ++ ") {\n" ++ then'' ++ "\n}" ++ maybe "" (\x -> " else {\n" ++ x ++ "\n}") else'' ++ ";"
  generateStatement (SExpression expr :>: _) = do
    let expr' = generateExpression expr
    expr' ++ ";"
  generateStatement (SReturn expr :>: _) = do
    let expr' = generateExpression expr
    "return " ++ expr' ++ ";"
  generateStatement (SConstant (name :@ ret) expr :>: _) = do
    let expr' = generateExpression expr
    "const " ++ ret ++ " " ++ name ++ " = " ++ expr' ++ ";"
  generateStatement (SModified name expr :>: _) = do
    let name' = generateExpression name
    let expr' = generateExpression expr
    name' ++ " = " ++ expr' ++ ";"
    
  generateExpression :: Located (Expression CType) -> String
  generateExpression (ECall n xs _ :>: _) = do
    let n' = generateExpression n
    let xs' = map generateExpression xs
    n' ++ "(" ++ intercalate "," xs' ++ ")"
  generateExpression (EBinaryOp op x y :>: _) = do
    let x' = generateExpression x
    let y' = generateExpression y
    x' ++ " " ++ op ++ " " ++ y'
  generateExpression (EUnaryOp op x :>: _) = do
    let x' = generateExpression x
    op ++ x'
  generateExpression (ETernary cond x y :>: _) = do
    let cond' = generateExpression cond
    let x' = generateExpression x
    let y' = generateExpression y
    cond' ++ " ? " ++ x' ++ " : " ++ y'
  generateExpression (EArrayLiteral xs :>: _) = do
    let xs' = map generateExpression xs
    "{" ++ intercalate "," xs' ++ "}"
  generateExpression (EStructureLiteral xs :>: _) = do
    let xs' = map (second generateExpression) xs
    "{" ++ intercalate "," (map (\(n, x) -> n ++ ":" ++ x) xs') ++ "}"
  generateExpression (EArrayAccess x y :>: _) = do
    let x' = generateExpression x
    let y' = generateExpression y
    x' ++ "[" ++ y' ++ "]"
  -- generateExpression (ELambda free ret args body :>: _) = do
  --   let free' = map ("&"++) free
  --   let body' = generateExpression body
  --   let args' = map (\(n :@ t) -> t ++ " " ++ n) args
  --   "[" ++ intercalate ", " free' ++ "](" ++ intercalate ", " args' ++ ") -> " ++ ret ++ " {\n return " ++ body' ++ "; \n}"
  generateExpression (ELambda _ _ _ _ :>: _) = error "not supported yet"
  generateExpression (EStructureAccess x y :>: _) = do
    let x' = generateExpression x
    x' ++ "." ++ y
  generateExpression (ECast t x :>: _) = do
    let x' = generateExpression x
    "(" ++ t ++ ")" ++ x'
  generateExpression (EReference x :>: _) = do
    let x' = generateExpression x
    "&" ++ x'
  generateExpression (EDereference x :>: _) = do
    let x' = generateExpression x
    "(*" ++ x' ++ ")"
  generateExpression (EBlock xs :>: _) = do
    let xs' = map generateStatement xs
    "{" ++ intercalate "" xs' ++ "}"
  generateExpression (EVariable "null" _ _ :>: _) = "NULL"
  generateExpression (EVariable n _ _ :>: _) = n
  generateExpression (ELiteral l :>: _) = generateLiteral l
  generateExpression (ESizeOf t :>: _) = "sizeof(" ++ t ++ ")"
  generateExpression _ = ""

  generateLiteral :: Literal -> String
  generateLiteral (IntLit x) = show x
  generateLiteral (FloatLit x) = show x
  generateLiteral (CharLit x) = show x
  generateLiteral (StringLit x) = show x
  
  
  