module Core.Parser.AST.Expression where
  import Core.Parser.AST.Literal (Literal, Located)
  import Data.Bifunctor (Bifunctor(bimap))
  import Data.List
  import Core.Color
  
  data Annoted a b = a :@ b
    deriving (Eq, Functor, Foldable, Ord)

  instance Traversable (Annoted a) where
    traverse f (a :@ b) = (a:@) <$> f b

  instance (Show a, Show b) => Show (Annoted a b) where
    show (a :@ b) = show a ++ ": " ++ show b

  instance {-# OVERLAPS #-} Show a => Show (Annoted String a) where
    show (a :@ b) = a ++ ": " ++ show b

  instance Bifunctor Annoted where
    bimap f g (x :@ y) = f x :@ g y

  data Declaration 
    = DChar | DInt | DFloat 
    | DCast [Declaration]
    | DId String
    | DFunction [String] Declaration [Declaration]
    | DApp Declaration Declaration
    | DPointer Declaration
    | DVoid
    deriving Eq

  showAnnots :: [String] -> String
  showAnnots [] = ""
  showAnnots xs = "<" ++ intercalate ", " xs ++ ">"

  instance Show Declaration where
    show DChar = "char"
    show DInt = "number"
    show DFloat = "float"
    show (DCast gens) = "<" ++ intercalate ", " (map show gens) ++ ">"
    show (DId s) = s
    show (DFunction annots ret args) = showAnnots annots ++ "(" ++ intercalate ", " (map show args) ++ ") => " ++ show ret
    show (DPointer t) = show t ++ "*"
    show DVoid = "void"
    show (DApp f x) = show f ++ "<" ++ show x ++ ">"

  data ImportMeta
    = IAll
    | IOnly [String]
    | INone
    deriving Eq

  instance Show ImportMeta where
    show IAll = "*"
    show (IOnly xs) = "{" ++ intercalate ", " xs ++ "}"
    show INone = ""
  
  -- 'a' represents the type of the expression
  data Toplevel a
    = TAssignment (Annoted String a) (Located (Expression a))
    | TImport ImportMeta String
    | TExport (Located (Toplevel a))
    | TDeclaration (Annoted String a)
    | TDeclarationFunction (Annoted String a) [a]
    | TEnumeration String [String]
    | TFunction [String] a String [Annoted String a] [Located (Statement a)]
    | TStructure [a] String [Annoted String a]
    | TConstant (Annoted String a) (Located (Expression a))
    | TType String a
    deriving Eq
  
  instance Show a => Show (Toplevel a) where
    show (TAssignment (name :@ t) expr) = bBlue "let " ++ name ++ " : " ++ show t ++ " = " ++ show expr
    show (TImport INone path) = bBlue "import " ++ path
    show (TImport meta path) = bBlue "import " ++ show meta ++ bBlue " from " ++ path
    show (TExport t) = bBlue "export " ++ show t
    show (TDeclarationFunction (name :@ t) args) = bBlue "declare function " ++ name ++ "(" ++ intercalate ", " (map show args) ++ "): " ++ show t
    show (TDeclaration (name :@ t)) = bBlue "declare " ++ name ++ " : " ++ show t
    show (TEnumeration name xs) = bBlue "enum " ++ name ++ " = " ++ intercalate ", " xs
    show (TFunction annots ret name args body) = bBlue "function " ++ name ++ showAnnots annots ++ "(" ++ intercalate ", " (map show args) ++ ")" ++ ": " ++ show ret ++ " {\n" ++ concatMap (("  "++) . (++";\n") . show) body ++ "}"
    show (TStructure gen name fields) = bBlue "interface " ++ name ++ showAnnots (map show gen) ++ " { " ++ intercalate ", " (map show fields) ++ " }"
    show (TType name t) = bBlue "type " ++ name ++ " = " ++ show t
    show (TConstant (name :@ t) expr) = bBlue "const " ++ name ++ " : " ++ show t ++ " = " ++ show expr

  data Statement a 
    = SAssignment (Annoted String a) (Located (Expression a))
    | SConstant (Annoted String a) (Located (Expression a))
    | SExpression (Located (Expression a))
    | SReturn (Located (Expression a))
    | SModified (Located (Expression a)) (Located (Expression a))
    | SIf (Located (Expression a)) (Located (Expression a)) (Maybe (Located (Expression a)))
    deriving Eq
  
  instance Show a => Show (Statement a) where
    show (SAssignment (name :@ t) expr) = bBlue "let " ++ name ++ ": " ++ show t ++ " = " ++ show expr
    show (SConstant (name :@ t) expr) = bBlue "const " ++ name ++ ": " ++ show t ++ " = " ++ show expr
    show (SExpression expr) = show expr
    show (SModified name expr) = show name ++ " = " ++ show expr
    show (SReturn expr) = bBlue "return " ++ show expr
    show (SIf cond then' else') = bBlue "if " ++ show cond ++ " { " ++ show then' ++ " } " ++ maybe "" (\e -> bBlue "else { " ++ show e ++ " }") else'

  data Expression a 
    = EVariable String a [a]
    | ECall (Located (Expression a)) [Located (Expression a)] a
    | ELiteral Literal
    | ELambda [String] a [Annoted String a] (Located (Expression a)) a
    | EArrayLiteral [Located (Expression a)]
    | EStructureLiteral [(String, Located (Expression a))]
    | ECast a (Located (Expression a))
    | ETernary (Located (Expression a)) (Located (Expression a)) (Located (Expression a))
    | EStructureAccess (Located (Expression a)) String
    | EArrayAccess (Located (Expression a)) (Located (Expression a))
    | EReference (Located (Expression a))
    | EDereference (Located (Expression a))
    | EBinaryOp String (Located (Expression a)) (Located (Expression a))
    | EUnaryOp String (Located (Expression a))
    | EBlock [Located (Statement a)]

    -- INTERNAL USE ONLY
    | ELetIn (Annoted String a) (Located (Expression a)) (Located (Expression a))
    | ESizeOf a
    deriving Eq
  
  instance Show a => Show (Expression a) where
    show (EVariable name _ _) = bold name{- ++ showAnnots (map show t)-}
    show (ECall f args _) = show f ++ "(" ++ intercalate ", " (map show args) ++ ")"
    show (ELiteral l) = show l
    show (ELambda annots ret args body _) = showAnnots annots ++ "(" ++ intercalate ", " (map show args) ++ "): " ++ show ret ++ " => " ++ show body
    show (EArrayLiteral xs) = "[" ++ intercalate ", " (map show xs) ++ "]"
    show (EStructureLiteral xs) = "{ " ++ intercalate ", " (map (\(k, v) -> k ++ ": " ++ show v) xs) ++ " }"
    show (ECast t expr) = "(" ++ show t ++ ") " ++ show expr
    show (ETernary cond then' else') = show cond ++ " ? " ++ show then' ++ " : " ++ show else'
    show (EStructureAccess expr name) = show expr ++ "." ++ name
    show (EArrayAccess expr index) = show expr ++ "[" ++ show index ++ "]"
    show (EReference expr) = "&" ++ show expr
    show (EDereference expr) = "*" ++ show expr
    show (EBinaryOp op a b) = show a ++ " " ++ op ++ " " ++ show b
    show (EUnaryOp op a) = op ++ show a
    show (EBlock xs) = "{ " ++ concatMap ((++";") . show) xs ++ " }"
    show (ELetIn (name :@ t) expr body) = "(" ++ bBlue "let " ++ name ++ ": " ++ show t ++ " = " ++ show expr ++ " in " ++ show body ++ ")"
    show (ESizeOf t) = "sizeof(" ++ show t ++ ")"