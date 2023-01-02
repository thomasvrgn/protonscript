{-# LANGUAGE LambdaCase #-}
module Core.Parser.Parser where
  import Text.Parsec.String
  import Core.Parser.AST.Expression
  import Core.Parser.AST.Literal
  import Core.Parser.Lexer (whiteSpace, parens, identifier, reservedOp, semi, comma, reserved, lexer, commaSep, integer, languageDef)
  import Text.Parsec
  import Text.Parsec.Expr
  import Control.Applicative (Alternative(some))
  import Data.Functor
  import Data.Functor.Identity (Identity)
  import qualified Text.Parsec.Token as Token
  import Data.Maybe

  type Proton a = Parser (Located a)

  parser :: Proton (Toplevel (Maybe Declaration))
  parser = whiteSpace *> topLevel

  locate :: Parser a -> Proton a
  locate p = do
    start <- getPosition
    r <- p
    end <- getPosition
    return (r :>: (start, end))

  {- TOPLEVEL PARSING -}

  topLevel :: Proton (Toplevel (Maybe Declaration))
  topLevel = choice [
      tExport <?> "export statement",
      tImport <?> "import statement",
      tConstant <?> "constant declaration",
      tDeclaration <?> "declaration",
      tAssignment <?> "assignment",
      tEnumeration <?> "enumeration",
      try (tFunction <?> "function"),
      try (tStructure <?> "structure")
    ]

  tDeclaration :: Proton (Toplevel (Maybe Declaration))
  tDeclaration = do
    s <- getPosition
    reserved "declare"
    (t, n) <- 
        (do
        reserved "function"
        name <- identifier
        gens <- getGenerics
        args <- catMaybes . map (snd . unannotate) <$> getArgs
        ty <- reserved ":" *> declaration
        return (DFunction gens ty args, name))
      <|> (do
        reserved "const" <|> reserved "let" <|> reserved "var"
        name <- identifier
        ty <- reserved ":" *> declaration
        return (ty, name))
    e <- getPosition
    return (TDeclaration (n :@ Just t) :>: (s, e))
    
  unannotate :: Annoted a b -> (a, b)
  unannotate (a :@ b) = (a, b)

  -- <type> <identifier> = <expression>
  tAssignment :: Proton (Toplevel (Maybe Declaration))
  tAssignment = do
    s <- getPosition
    reserved "var" <|> reserved "let"
    name <- identifier
    ty <- optionMaybe $ reservedOp ":" *> declaration
    reservedOp "="
    expr <- expression
    e <- getPosition
    return $ TAssignment (name :@ ty) expr :>: (s, e)
  
  tExport :: Proton (Toplevel (Maybe Declaration))
  tExport = do
    s <- getPosition
    reserved "export"
    name <- topLevel
    e <- getPosition
    return $ TExport name :>: (s, e)

  tImport :: Proton (Toplevel (Maybe Declaration))
  tImport = do
    s <- getPosition
    reserved "import"
    meta <- iMeta
    name <- Token.stringLiteral lexer
    e <- getPosition
    return $ TImport meta name :>: (s, e)

  tEnumeration :: Proton (Toplevel (Maybe Declaration))
  tEnumeration = do
    s <- getPosition
    reserved "enum"
    name <- identifier
    reservedOp "{"
    values <- identifier `sepBy` comma
    reservedOp "}"
    e <- getPosition
    return $ TEnumeration name values :>: (s, e)

  operator :: ParsecT String () Identity String
  operator = do
    let operators = Token.reservedOpNames languageDef
    choice $ map (\x -> reserved x >> return x) operators

  tFunction :: Proton (Toplevel (Maybe Declaration))
  tFunction = do
    s <- getPosition
    reserved "function"
    name <- operator <|> identifier
    generics <- option [] $ Token.angles lexer $ commaSep identifier
    args <- parens $ ((:@) <$> identifier <*> optionMaybe (reservedOp ":" *> declaration)) `sepBy` comma
    ty <- optionMaybe $ reservedOp ":" *> declaration
    body <- block
    e <- getPosition
    return $ TFunction generics ty name args body :>: (s, e)

  tConstant :: Proton (Toplevel (Maybe Declaration))
  tConstant = do
    s <- getPosition
    reserved "const"
    name <- identifier
    ty <- optionMaybe $ reservedOp ":" *> declaration
    reservedOp "="
    expr <- expression
    e <- getPosition
    return $ TConstant (name :@ ty) expr :>: (s, e)

  tStructure :: Proton (Toplevel (Maybe Declaration))
  tStructure = do
    s <- getPosition
    reserved "interface"
    name <- identifier
    generics <- map (Just . DId) <$> getGenerics
    reservedOp "{"
    fields <- many $ ((:@) <$> (identifier <* reservedOp ":") <*> (Just <$> declaration)) <* semi
    reservedOp "}"
    e <- getPosition
    return $ TStructure generics name fields :>: (s, e)

  iMeta :: Parser ImportMeta
  iMeta = choice [
      (reservedOp "*" >> return IAll) <* reserved "from",
      (Token.braces lexer (commaSep identifier) <&> IOnly) <* reserved "from",
      return INone
    ]
  
  {- STATEMENT PARSING -}

  statement :: Proton (Statement (Maybe Declaration))
  statement = choice [
      sModified <?> "variable modification",
      sConstant <?> "constant declaration",
      sAssignment <?> "assignment",
      sReturn <?> "return",
      sIf <?> "condition",
      sExpression <?> "expression term"
    ]

  sModified :: Proton (Statement (Maybe Declaration))
  sModified = do
    s <- getPosition
    name <- try $ expression <* reservedOp "="
    e <- expression
    s2 <- getPosition
    return (SModified name e :>: (s, s2))

  sAssignment :: Proton (Statement (Maybe Declaration))
  sAssignment = tAssignment >>= \case
    TAssignment name expr :>: p -> return $ SAssignment name expr :>: p
    _ -> error "impossible"
  
  sConstant :: Proton (Statement (Maybe Declaration))
  sConstant = tConstant >>= \case
    TConstant name expr :>: p -> return $ SConstant name expr :>: p
    _ -> error "impossible"

  sExpression :: Proton (Statement (Maybe Declaration))
  sExpression = do
    e@(_ :>: p) <- expression
    return $ SExpression e :>: p

  sReturn :: Proton (Statement (Maybe Declaration))
  sReturn = do
    s <- getPosition
    reserved "return"
    expr <- expression
    e <- getPosition
    return $ SReturn expr :>: (s, e)

  sIf :: Proton (Statement (Maybe Declaration))
  sIf = do
    s <- getPosition
    reserved "if"
    cond <- parens expression
    then' <- expression
    else' <- optionMaybe $ reserved "else" *> expression
    e <- getPosition
    return $ SIf cond then' else' :>: (s, e)

  {- EXPRESSION PARSING -}

  expression :: Proton (Expression (Maybe Declaration))
  expression = buildExpressionParser table expressionTerm
    where
      table = [
          [ Postfix $ makeUnaryOp postfix ],
          [ Prefix $ makeUnaryOp prefix ],
          equalities,
          [ Postfix $ do
              reserved "?"
              thn <- expression
              reserved ":"
              els <- expression
              return (\x@(_ :>: (p, _)) -> ETernary x thn els :>: (p, snd $ loc els)) ],
          [ Infix (reservedOp "*" >> return (\x@(_ :>: (s, _)) y@(_ :>: (_, e)) -> EBinaryOp "*" x y :>: (s, e))) AssocLeft,
            Infix (reservedOp "/" >> return (\x@(_ :>: (s, _)) y@(_ :>: (_, e)) -> EBinaryOp "/" x y :>: (s, e))) AssocLeft ],
          [ Infix (reservedOp "+" >> return (\x@(_ :>: (s, _)) y@(_ :>: (_, e)) -> EBinaryOp "+" x y :>: (s, e))) AssocLeft,
            Infix (reservedOp "-" >> return (\x@(_ :>: (s, _)) y@(_ :>: (_, e)) -> EBinaryOp "-" x y :>: (s, e))) AssocLeft ]
        ]
      postfix = call <|> pointer <|> object <|> index <|> castPostfix
      castPostfix = do
        reserved "as"
        ty <- declaration
        e <- getPosition
        return (\x@(_ :>: (p, _)) -> ECast (Just ty) x :>: (p, e))
      call = do
        args <- parens $ commaSep expression
        e <- getPosition
        return $ \x@(_ :>: (s, _)) -> ECall x args Nothing :>: (s, e)
      pointer = do
        reservedOp "->"
        name <- identifier
        e <- getPosition
        return $ \x@(_ :>: (s, e')) -> EStructureAccess (EDereference x :>: (s, e')) name :>: (s, e)
      object = do
        reservedOp "."
        object' <- identifier
        e <- getPosition
        return $ \x@(_ :>: (_, s)) -> EStructureAccess x object' :>: (e, s)
      index = do
        index' <- Token.brackets lexer expression
        e <- getPosition
        return $ \x@(_ :>: (p, _)) -> EArrayAccess x index' :>: (p, e)

      equalityOp = ["==", "!=", "<", ">", "<=", ">="]
      equalities = map (\op -> Infix (reservedOp op >> return (\x@(_ :>: (s, _)) y@(_ :>: (_, e)) -> EBinaryOp op x y :>: (s, e))) AssocLeft) equalityOp

      prefix = ref <|> unref
      ref = do
        s <- getPosition
        reservedOp "&"
        return $ \x@(_ :>: (_, e)) -> EReference x :>: (s, e)
      unref = do
        s <- getPosition
        reservedOp "*"
        return $ \x@(_ :>: (_, e)) -> EDereference x :>: (s, e)

  expressionTerm :: Proton (Expression (Maybe Declaration))
  expressionTerm = choice [
      eLiteral <?> "literal",
      eArrayLiteral <?> "array literal",
      try eLambda <?> "anonymous function",
      try eStructureLiteral <?> "structure literal",
      eBlock,
      eSizeof <?> "type size",
      eVariable <?> "variable",
      parens expression
    ]
  
  eSizeof :: Proton (Expression (Maybe Declaration))
  eSizeof = do
    s <- getPosition
    reserved "sizeof"
    t <- declaration
    e <- getPosition
    return $ ESizeOf (Just t) :>: (s, e)

  getArgs :: Parser [Annoted String (Maybe Declaration)]
  getArgs = parens $ ((:@) <$> identifier <*> optionMaybe (reservedOp ":" *> declaration)) `sepBy` comma

  getGenerics :: ParsecT String () Identity [String]
  getGenerics = option [] $ Token.angles lexer $ commaSep identifier

  eLambda :: Proton (Expression (Maybe Declaration))
  eLambda = do
    s <- getPosition
    (generics, args, ty) <- 
      (((,,) <$> getGenerics <*> getArgs <*> (optionMaybe $ reservedOp ":" *> declaration)) <* reservedOp "=>") 
      <|> 
      (reserved "function" *> ((,,) <$> getGenerics <*> getArgs <*> (optionMaybe $ reservedOp ":" *> declaration)))
    body <- expression
    e <- getPosition
    return $ ELambda generics ty args body Nothing :>: (s, e)

  eBlock :: Proton (Expression (Maybe Declaration))
  eBlock = do
    s <- getPosition
    body <- block
    e <- getPosition
    return $ EBlock body :>: (s, e)

  eLiteral :: Proton (Expression (Maybe Declaration))
  eLiteral = do
    l :>: p <- literal
    return $ ELiteral l :>: p

  eVariable :: Proton (Expression (Maybe Declaration))
  eVariable = do
    s <- getPosition
    name <- identifier
    gens <- option [] (Token.angles lexer $ commaSep declaration)
    e <- getPosition
    return $ EVariable name Nothing (map Just gens) :>: (s, e)

  eArrayLiteral :: Proton (Expression (Maybe Declaration))
  eArrayLiteral = do
    s <- getPosition
    reservedOp "["
    exprs <- expression `sepBy` comma
    reservedOp "]"
    e <- getPosition
    return $ EArrayLiteral exprs :>: (s, e)

  eStructureLiteral :: Proton (Expression (Maybe Declaration))
  eStructureLiteral = do
    s <- getPosition
    fields <- Token.braces lexer $ ((,) <$> identifier <*> (reservedOp ":" *> expression)) `sepBy` comma
    e <- getPosition
    return $ EStructureLiteral fields :>: (s, e)

  {- DECLARATION PARSING -}

  buildFun :: [Declaration] -> Declaration -> Declaration
  buildFun xs t = go (reverse xs) t
    where go [] t' = t'
          go (x:xs') t' = DApp (go xs' t') x

  declaration :: Parser Declaration
  declaration = buildExpressionParser table declarationTerm
    where
      table = [[ Postfix $ makeUnaryOp postfix ]]
      postfix = app
      app = do
        args <- Token.angles lexer $ commaSep declaration
        return $ \x -> buildFun args x

  declarationTerm :: Parser Declaration
  declarationTerm =  (reserved "char"   $> DChar)
                 <|> (reserved "number" $> DInt)
                 <|> (reserved "float"  $> DFloat)
                 <|> (reserved "void"   $> DVoid)
                 <|> (reserved "string" $> DPointer DChar)
                 <|> (identifier       <&> DId)
                 <|> try (do 
                            generics <- option [] $ Token.angles lexer $ commaSep identifier
                            args <- parens $ commaSep (identifier *> reservedOp ":" *> declaration)
                            reservedOp "=>"
                            ret <- declaration
                            return $ DFunction generics ret args)
                 <|> parens declaration

  {- LITERAL PARSING -}

  literal :: Proton Literal
  literal = choice [
      lInt <?> "integer literal",
      lFloat <?> "float literal",
      lChar <?> "character literal",
      lString <?> "string literal"
    ]

  lInt :: Proton Literal
  lInt = do
    s <- getPosition
    n <- integer
    e <- getPosition
    return $ IntLit (fromInteger n) :>: (s, e)

  lFloat :: Proton Literal
  lFloat = do
    s <- getPosition
    n <- Token.float lexer
    e <- getPosition
    return $ FloatLit n :>: (s, e)

  lChar :: Proton Literal
  lChar = do
    s <- getPosition
    c <- Token.charLiteral lexer
    e <- getPosition
    return $ CharLit c :>: (s, e)

  lString :: Proton Literal
  lString = do
    s <- getPosition
    str <- Token.stringLiteral lexer
    e <- getPosition
    return $ StringLit str :>: (s, e)

  {- UTILITY PARSING -}

  type ProtonOP a = Operator String () Identity a

  makeUnaryOp :: Alternative f => f (a -> a) -> f (a -> a)
  makeUnaryOp s = foldr1 (.) . reverse <$> some s

  binary :: Parser (a -> a -> a) -> ProtonOP a
  binary p = Infix p AssocLeft

  block :: Parser [Located (Statement (Maybe Declaration))]
  block = Token.braces lexer $ many (statement <* optionMaybe semi)

  loc :: Located a -> (SourcePos, SourcePos)
  loc (_ :>: p) = p

  parseProton :: String -> String -> Either ParseError [Located (Toplevel (Maybe Declaration))]
  parseProton = runParser (many (parser <* optionMaybe semi) <* eof) ()