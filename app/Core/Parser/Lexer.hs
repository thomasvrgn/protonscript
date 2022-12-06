module Core.Parser.Lexer where
  import qualified Text.Parsec.Token as Token
  import Text.Parsec.Token (GenTokenParser)
  import Data.Functor.Identity (Identity)
  import Text.Parsec.String (Parser)
  import Text.Parsec.Language (emptyDef)
  import Text.Parsec (letter, alphaNum)

  languageDef :: Token.GenLanguageDef String u Identity
  languageDef =
    emptyDef {  Token.commentStart    = "/*"
              , Token.commentEnd      = "*/"
              , Token.commentLine     = "//"
              , Token.identStart      = letter
              , Token.identLetter     = alphaNum
              , Token.reservedNames   = ["var", "let", "const", "function", "interface", "enum", "type", "return", "if", "else"]
              , Token.reservedOpNames = ["+", "-", "*", "/", "%", "_", "=>"] }

  lexer :: GenTokenParser String u Identity
  lexer = Token.makeTokenParser languageDef

  identifier :: Parser String
  identifier = Token.identifier lexer

  reserved :: String -> Parser ()
  reserved = Token.reserved lexer

  reservedOp :: String -> Parser ()
  reservedOp = Token.reservedOp lexer

  parens :: Parser a -> Parser a
  parens = Token.parens lexer

  integer :: Parser Integer
  integer = Token.integer lexer

  whiteSpace :: Parser ()
  whiteSpace = Token.whiteSpace lexer

  comma :: Parser String
  comma = Token.comma lexer

  commaSep :: Parser a -> Parser [a]
  commaSep = Token.commaSep lexer

  semi :: Parser String
  semi = Token.semi lexer