module Core.Compiler.Compiler where
  import Core.Parser.AST.Expression
  import Core.Parser.AST.Literal
  import Core.Checker.Definition.Type
  import Data.List
  import Control.Monad.State
  import Core.Transformation.Free
  import qualified Data.Map as M

  type CType = String
  type IR f = Located (f CType)

  type ToplevelIR = IR Toplevel
  type ExpressionIR = IR Expression
  type StatementIR = IR Statement
  
  data CompilerState = CompilerState {
    counter :: Int,
    declarations :: [String],
    functions :: [String]
  }
  type MonadCompiler m = MonadState CompilerState m

  freshTypeName :: MonadCompiler m => m String
  freshTypeName = do
    n <- gets counter
    modify $ \s -> s { counter = n + 1 }
    return $ "lambda" ++ show n
  
  addDeclaration :: MonadCompiler m => String -> m ()
  addDeclaration name 
    = modify $ \s -> s { declarations = name : declarations s }

  fromType :: MonadCompiler m => Type -> m CType
  fromType  Int = return "int"
  fromType  Bool = return "bool"
  fromType  Float = return "float"
  fromType  Char = return "char"
  fromType  Void = return "void"
  fromType  (TId n) = return $ "struct " ++ n
  fromType (args :-> ret) = do
    name <- freshTypeName
    args' <- mapM fromType args
    ret' <- fromType ret
    addDeclaration $ "typedef " ++ ret' ++ "(*" ++ name ++ ")(" ++ intercalate "," args' ++ ");"
    return name
    -- return $ "std::function<" ++ ret' ++ "(" ++ intercalate "," args' ++ ")>"
  fromType (TVar _) = return "void*"
  fromType (TRec _) = error "Should not happen"
  fromType (TPtr t) = (++"*") <$> fromType t
  fromType (TApp _ _) = return "void*"

  compileToplevel :: MonadCompiler m => Located (Toplevel Type) -> m ToplevelIR
  compileToplevel (TFunction annots ret name args body :>: pos) = do
    ret' <- fromType ret
    args' <- mapM (\(x :@ t) -> (x :@) <$> fromType t) args
    body' <- mapM compileStatement body
    return $ TFunction annots ret' name args' body' :>: pos
  compileToplevel (TAssignment (name :@ t) expr :>: pos) = do
    t' <- fromType t
    expr' <- compileExpression expr
    return $ TAssignment (name :@ t') expr' :>: pos
  compileToplevel (TDeclaration (name :@ t) :>: pos) = do
    modify $ \s -> s { functions = name : functions s }
    case t of
      args :-> ret -> do
        ret' <- fromType ret
        args' <- mapM fromType args
        return $ TDeclarationFunction (name :@ ret') args' :>: pos
      _ -> do
        t' <- fromType t
        return $ TDeclaration (name :@ t') :>: pos
  compileToplevel (TEnumeration name xs :>: pos)
    = return $ TEnumeration name xs :>: pos
  compileToplevel (TStructure gens name fields :>: pos) = do
    gens' <- mapM fromType gens
    fields' <- mapM (\(x :@ t) -> (x :@) <$> fromType t) fields
    return $ TStructure gens' name fields' :>: pos
  compileToplevel (TConstant (name :@ t) expr :>: pos) = do
    t' <- fromType t
    expr' <- compileExpression expr
    return $ TConstant (name :@ t') expr' :>: pos
  compileToplevel _ = error "Should not happen"

  compileStatement :: MonadCompiler m => Located (Statement Type) -> m StatementIR
  compileStatement (SAssignment (name :@ t) expr :>: pos) = do
    expr' <- compileExpression expr
    t' <- fromType t
    return $ SAssignment (name :@ t') expr' :>: pos
  compileStatement (SIf cond then' else' :>: pos) = do
    cond' <- compileExpression cond
    then'' <- compileExpression then'
    else'' <- case else' of
      Nothing -> return Nothing
      Just x -> do
        x' <- compileExpression x
        return $ Just x'
    return $ SIf cond' then'' else'' :>: pos
  compileStatement (SExpression expr :>: pos) = do
    expr' <- compileExpression expr
    return $ SExpression expr' :>: pos
  compileStatement (SReturn expr :>: pos) = do
    expr' <- compileExpression expr
    return $ SReturn expr' :>: pos
  compileStatement (SConstant (name :@ t) expr :>: pos) = do
    expr' <- compileExpression expr
    t' <- fromType t
    return $ SConstant (name :@ t') expr' :>: pos
  compileStatement (SModified name expr :>: pos) = do
    name' <- compileExpression name
    expr' <- compileExpression expr
    return $ SModified name' expr' :>: pos
    
  compileExpression :: MonadCompiler m => Located (Expression Type) -> m ExpressionIR
  compileExpression (ECall n xs t :>: pos) = do
    t' <- fromType t
    n' <- compileExpression n
    xs' <- mapM compileExpression xs
    return $ ECall n' xs' t' :>: pos
  compileExpression (EBinaryOp op x y :>: pos) = do
    x' <- compileExpression x
    y' <- compileExpression y
    return $ EBinaryOp op x' y' :>: pos
  compileExpression (EUnaryOp op x :>: pos) = do
    x' <- compileExpression x
    return $ EUnaryOp op x' :>: pos
  compileExpression (ETernary cond x y :>: pos) = do
    cond' <- compileExpression cond
    x' <- compileExpression x
    y' <- compileExpression y
    return $ ETernary cond' x' y' :>: pos
  compileExpression (EArrayLiteral xs :>: pos) = do
    xs' <- mapM compileExpression xs
    return $ EArrayLiteral xs' :>: pos
  compileExpression (EStructureLiteral xs :>: pos) = do
    xs' <- mapM (\(x, y) -> do
      y' <- compileExpression y
      return (x, y')) xs
    return $ EStructureLiteral xs' :>: pos
  compileExpression (EArrayAccess x y :>: pos) = do
    x' <- compileExpression x
    y' <- compileExpression y
    return $ EArrayAccess x' y' :>: pos
  compileExpression (EStructureAccess x y :>: pos) = do
    x' <- compileExpression x
    return $ EStructureAccess x' y :>: pos
  compileExpression (ECast t x :>: pos) = do
    x' <- compileExpression x
    t' <- fromType t
    return $ ECast t' x' :>: pos
  compileExpression (EReference x :>: pos) = do
    x' <- compileExpression x
    return $ EReference x' :>: pos
  compileExpression (EDereference x :>: pos) = do
    x' <- compileExpression x
    return $ EDereference x' :>: pos
  compileExpression (EBlock xs :>: pos) = do
    xs' <- mapM compileStatement xs
    return $ EBlock xs' :>: pos
  compileExpression (EVariable x t casts :>: pos) = do
    t' <- fromType t
    casts' <- mapM fromType casts
    return $ EVariable x t' casts' :>: pos
  compileExpression (ELiteral lit :>: pos) = return $ ELiteral lit :>: pos
  compileExpression (ESizeOf t :>: pos) = do
    t' <- fromType t
    return $ ESizeOf t' :>: pos
  compileExpression z@(ELambda _ ret args body :>: pos) = do
    ret' <- fromType ret
    args' <- mapM (\(x :@ t) -> (x :@) <$> fromType t) args
    body' <- compileExpression body
    funs <- gets functions
    let env = M.keys (free z) \\ funs
    return $ ELambda env ret' args' body' :>: pos
  compileExpression _ = error "Should not happen"

  compile :: Monad m => [Located (Toplevel Type)] -> m ([String], [ToplevelIR])
  compile xs = do
    (xs', CompilerState _ decls _) <- runStateT (mapM compileToplevel xs) (CompilerState 0 [] ["printf"])
    return (decls, xs')