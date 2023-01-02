{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
module Core.Optimizer.GarbageCollector where
  import Core.Checker.Definition.Type
  import Control.Monad.RWS
  import Core.Parser.AST.Expression
  import Core.Parser.AST.Literal
  import Data.Tuple.Extra

  type MonadGarbage m = (MonadRWS [String] () ([String], [String], [String]) m)

  garbageToplevel :: MonadGarbage m => Located (Toplevel Type) -> m (Located (Toplevel Type))
  garbageToplevel (TFunction annots ret name args body :>: pos) = do
    unless (name == "main") $ modify (first3 (name:))
    body' <- local (name:) $ mapM garbageStatement body
    garbageTy "" ret
    mapM_ (\(_ :@ t) -> garbageTy "" t) args
    return $ TFunction annots ret name args body' :>: pos
  garbageToplevel (TAssignment name@(n :@ t) expr :>: pos) = do
    unless (n == "main") $ modify (first3 (n:))
    garbageTy "" t
    expr' <- local (n:) $ garbageExpression expr
    return $ TAssignment name expr' :>: pos
  garbageToplevel (TConstant name@(n :@ t) expr :>: pos) = do
    unless (n == "main") $ modify (first3 (n:))
    expr' <- local (n:) $ garbageExpression expr
    garbageTy "" t
    return $ TConstant name expr' :>: pos
  garbageToplevel (TStructure gen name fields :>: pos) = do
    modify (second3 (name:))
    mapM (\(_ :@ t) -> garbageTy name t) fields
    return $ TStructure gen name fields :>: pos
  garbageToplevel x = return x

  garbageStatement :: MonadGarbage m => Located (Statement Type) -> m (Located (Statement Type))
  garbageStatement (SAssignment name@(n :@ t) expr :>: pos) = do
    unless (n == "main") $ modify (first3 (n:))
    expr' <- local (n:) $ garbageExpression expr
    garbageTy "" t
    return $ SAssignment name expr' :>: pos
  garbageStatement (SIf cond then' else' :>: pos) = do
    cond' <- garbageExpression cond
    then'' <- garbageExpression then'
    else'' <- case else' of
      Nothing -> return Nothing
      Just x -> do
        x' <- garbageExpression x
        return $ Just x'
    return $ SIf cond' then'' else'' :>: pos
  garbageStatement (SExpression expr :>: pos) = do
    expr' <- garbageExpression expr
    return $ SExpression expr' :>: pos
  garbageStatement (SReturn expr :>: pos) = do
    expr' <- garbageExpression expr
    return $ SReturn expr' :>: pos
  garbageStatement (SConstant name@(n :@ t) expr :>: pos) = do
    unless (n == "main") $ modify (first3 (n:))
    expr' <- local (n:) $ garbageExpression expr
    garbageTy "" t
    return $ SConstant name expr' :>: pos
  garbageStatement (SModified name expr :>: pos) = do
    expr' <- garbageExpression expr
    return $ SModified name expr' :>: pos
  
  garbageTy :: MonadGarbage m => String -> Type -> m Type
  garbageTy n (args :-> ret) = do
    args' <- mapM (garbageTy n) args
    ret' <- garbageTy n ret
    return $ args' :-> ret'
  garbageTy _ (TVar name) = return $ TVar name
  garbageTy n (TRec fs) = do
    fs' <- mapM (secondM (garbageTy n)) fs
    return $ TRec fs'
  garbageTy n' (TId n) = do
    unless (n' == n) $ modify (second3 $ filter (/=n))
    return $ TId n
  garbageTy n (TPtr t) = do
    t' <- garbageTy n t
    return $ TPtr t'
  garbageTy _ x = return x

  garbageExpression :: MonadGarbage m => Located (Expression Type) -> m (Located (Expression Type))
  garbageExpression (ECall n xs t :>: pos) = do
    n' <- garbageExpression n
    xs' <- mapM garbageExpression xs
    return $ ECall n' xs' t :>: pos
  garbageExpression (EBinaryOp op x y :>: pos) = do
    x' <- garbageExpression x
    y' <- garbageExpression y
    return $ EBinaryOp op x' y' :>: pos
  garbageExpression (EUnaryOp op x :>: pos) = do
    x' <- garbageExpression x
    return $ EUnaryOp op x' :>: pos
  garbageExpression (ETernary cond x y :>: pos) = do
    cond' <- garbageExpression cond
    x' <- garbageExpression x
    y' <- garbageExpression y
    return $ ETernary cond' x' y' :>: pos
  garbageExpression (EArrayLiteral xs :>: pos) = do
    xs' <- mapM garbageExpression xs
    return $ EArrayLiteral xs' :>: pos
  garbageExpression (EStructureLiteral xs :>: pos) = do
    xs' <- mapM (\(x, y) -> do
      y' <- garbageExpression y
      return (x, y')) xs
    return $ EStructureLiteral xs' :>: pos
  garbageExpression (EArrayAccess x y :>: pos) = do
    x' <- garbageExpression x
    y' <- garbageExpression y
    return $ EArrayAccess x' y' :>: pos
  garbageExpression (EStructureAccess x y :>: pos) = do
    x' <- garbageExpression x
    return $ EStructureAccess x' y :>: pos
  garbageExpression (ECast t x :>: pos) = do
    x' <- garbageExpression x
    return $ ECast t x' :>: pos
  garbageExpression (ELambda annots ret args body t :>: pos) = do
    body' <- garbageExpression body
    return $ ELambda annots ret args body' t :>: pos
  garbageExpression (EReference x :>: pos) = do
    x' <- garbageExpression x
    return $ EReference x' :>: pos
  garbageExpression (EDereference x :>: pos) = do
    x' <- garbageExpression x
    return $ EDereference x' :>: pos
  garbageExpression (EBlock xs :>: pos) = do
    xs' <- mapM garbageStatement xs
    (s, _, _) <- get
    return $ EBlock (filter (\case
      SAssignment (n :@ _) _ :>: _ -> notElem n s
      _ -> True) xs') :>: pos
  garbageExpression (EVariable name t d :>: pos) = do
    garbageTy "" t
    mapM_ (garbageTy "") d
    env <- ask
    modify (first3 $ filter (\x -> x /= name && notElem x env))
    return $ EVariable name t d :>: pos
  garbageExpression x = return x

  runGarbage :: Monad m => [Located (Toplevel Type)] -> m [Located (Toplevel Type)]
  runGarbage xs = do
    (xs', (env, structs, recur), _) <- runRWST (do
      xs' <- mapM garbageToplevel xs
      env <- ask
      modify $ third3 (const env)
      return xs') [] ([], [], [])
    return (filter (\case
      TAssignment (n :@ _) _ :>: _ -> notElem n env || notElem n recur
      TStructure _ n _ :>: _ -> notElem n structs
      _ -> True) xs')
