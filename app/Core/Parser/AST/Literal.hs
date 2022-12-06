module Core.Parser.AST.Literal where
  import Text.Parsec (SourcePos)
  import Core.Color

  type Position = (SourcePos, SourcePos)

  data Located a
    = a :>: Position
    deriving Eq
  
  instance Show a => Show (Located a) where
    show (a :>: _) = show a

  data Literal
    = IntLit Integer 
    | FloatLit Double
    | StringLit String
    | CharLit Char
    deriving Eq
  
  instance Show Literal where
    show (IntLit i) = bYellow $ show i
    show (FloatLit f) = bYellow $ show f
    show (StringLit s) = bGreen $ show s
    show (CharLit c) = bGreen $ show c