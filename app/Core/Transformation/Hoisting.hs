module Core.Transformation.Hoisting where
  import Core.Checker.Definition.Type
  import Control.Monad.RWS
  import Core.Parser.AST.Expression
  import Core.Parser.AST.Literal
  import Core.Checker.Checker

  type MonadHoist m = (MonadRWS () [Located (Toplevel Type)] Int m)
  
  freshName :: MonadHoist m => m String
  freshName = do
    i <- get
    put (i+1)
    return $ "$lambda" ++ show i

  hoistToplevel :: MonadHoist m => Located (Toplevel Type) -> m (Located (Toplevel Type))
  hoistToplevel (TFunction annots ret name args body :>: pos) = do
    body' <- mapM hoistStatement body
    return $ TFunction annots ret name args body' :>: pos
  hoistToplevel (TAssignment name expr :>: pos) = do
    expr' <- hoistExpression expr
    return $ TAssignment name expr' :>: pos
  hoistToplevel (TConstant name expr :>: pos) = do
    expr' <- hoistExpression expr
    return $ TConstant name expr' :>: pos
  hoistToplevel x = return x

  hoistStatement :: MonadHoist m => Located (Statement Type) -> m (Located (Statement Type))
  hoistStatement (SAssignment name expr :>: pos) = do
    expr' <- hoistExpression expr
    return $ SAssignment name expr' :>: pos
  hoistStatement (SIf cond then' else' :>: pos) = do
    cond' <- hoistExpression cond
    then'' <- hoistExpression then'
    else'' <- case else' of
      Nothing -> return Nothing
      Just x -> do
        x' <- hoistExpression x
        return $ Just x'
    return $ SIf cond' then'' else'' :>: pos
  hoistStatement (SExpression expr :>: pos) = do
    expr' <- hoistExpression expr
    return $ SExpression expr' :>: pos
  hoistStatement (SReturn expr :>: pos) = do
    expr' <- hoistExpression expr
    return $ SReturn expr' :>: pos
  hoistStatement (SConstant name expr :>: pos) = do
    expr' <- hoistExpression expr
    return $ SConstant name expr' :>: pos
  hoistStatement (SModified name expr :>: pos) = do
    expr' <- hoistExpression expr
    return $ SModified name expr' :>: pos
    
  hoistExpression :: MonadHoist m => Located (Expression Type) -> m (Located (Expression Type))
  hoistExpression (ECall n xs t :>: pos) = do
    n' <- hoistExpression n
    xs' <- mapM hoistExpression xs
    return $ ECall n' xs' t :>: pos
  hoistExpression (EBinaryOp op x y :>: pos) = do
    x' <- hoistExpression x
    y' <- hoistExpression y
    return $ EBinaryOp op x' y' :>: pos
  hoistExpression (EUnaryOp op x :>: pos) = do
    x' <- hoistExpression x
    return $ EUnaryOp op x' :>: pos
  hoistExpression (ETernary cond x y :>: pos) = do
    cond' <- hoistExpression cond
    x' <- hoistExpression x
    y' <- hoistExpression y
    return $ ETernary cond' x' y' :>: pos
  hoistExpression (EArrayLiteral xs :>: pos) = do
    xs' <- mapM hoistExpression xs
    return $ EArrayLiteral xs' :>: pos
  hoistExpression (EStructureLiteral xs :>: pos) = do
    xs' <- mapM (\(x, y) -> do
      y' <- hoistExpression y
      return (x, y')) xs
    return $ EStructureLiteral xs' :>: pos
  hoistExpression (EArrayAccess x y :>: pos) = do
    x' <- hoistExpression x
    y' <- hoistExpression y
    return $ EArrayAccess x' y' :>: pos
  hoistExpression (EStructureAccess x y :>: pos) = do
    x' <- hoistExpression x
    return $ EStructureAccess x' y :>: pos
  hoistExpression (ECast t x :>: pos) = do
    x' <- hoistExpression x
    return $ ECast t x' :>: pos
  hoistExpression (ELambda annots ret args body :>: pos) = do
    body' <- hoistExpression body
    name <- freshName
    tell [TFunction annots ret name args (case body' of
      EBlock blocks :>: _ -> blocks
      _ -> [SReturn body' :>: pos]) :>: pos]
    return $ EVariable name (map (snd . unannotate) args :-> ret) [] :>: pos
  hoistExpression (EReference x :>: pos) = do
    x' <- hoistExpression x
    return $ EReference x' :>: pos
  hoistExpression (EDereference x :>: pos) = do
    x' <- hoistExpression x
    return $ EDereference x' :>: pos
  hoistExpression (EBlock xs :>: pos) = do
    xs' <- mapM hoistStatement xs
    return $ EBlock xs' :>: pos
  hoistExpression x = return x

  runHoisting :: Monad m => [Located (Toplevel Type)] -> m [Located (Toplevel Type)]
  runHoisting xs = do
    (xs', _, lambdas) <- runRWST (mapM hoistToplevel xs) () 0
    return (lambdas ++ xs')