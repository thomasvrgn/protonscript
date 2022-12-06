module Core.Checker.Definition.Type where
  import Data.Map (Map)
  import Data.List (intercalate)
  
  data Type
    = TVar Int
    | [Type] :-> Type
    | Int | Float | Bool | Char | Void
    | TRec [(String, Type)]
    | TId String
    | TApp Type Type
    | TPtr Type
    deriving (Eq, Ord)

  type TypeEnv = Map String Scheme
  type ConsEnv = Map Type Scheme
  type Env = (TypeEnv, ConsEnv)

  -- Bool indicates whether the type is public or not
  data Scheme = Forall Bool [Int] Type
    deriving (Eq, Ord, Show)

  instance Show Type where
    show (TVar i) = "t" ++ show i
    show (t :-> u) = "(" ++ intercalate ", " (map show t) ++ ") => " ++ show u
    show Int = "number"
    show Void = "void"
    show Float = "float"
    show Bool = "boolean"
    show Char = "char"
    show (TRec fs) = "{ " ++ intercalate ", " (map (\(n, t) -> n ++ ": " ++ show t) fs) ++ " }"
    show (TPtr Char) = "string"
    show (TPtr t) = "Ref<" ++ show t ++ ">"
    show (TId s) = s
    show (TApp s args) = show s ++ ("<" ++ show args ++ ">")