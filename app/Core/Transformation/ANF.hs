module Core.Transformation.ANF where
  import Core.Checker.Definition.Type
  import Control.Monad.RWS
  import Core.Parser.AST.Expression
  import Core.Parser.AST.Literal
  import Data.List

  type MonadANF m = (MonadRWS [(String, String)] [Located (Toplevel Type)] Int m)

  freshName :: MonadANF m => m String
  freshName = do
    i <- get
    put (i+1)
    return $ "$a" ++ show i

  anfToplevel :: MonadANF m => Located (Toplevel Type) -> m ([(Annoted String Type, Located (Expression Type))], Located (Toplevel Type))
  anfToplevel (TFunction annots ret name args body :>: pos) = do
    (lets, body') <- unzip <$> mapM anfStatement body
    let lets' = map (\xs -> map (\(x, e@(_ :>: pos')) ->
            SAssignment x e :>: pos') xs) lets
    let xs = concatMap (\(lets'', x) -> lets'' ++ [x]) (zip lets' body')
    return $ ([], TFunction annots ret name args xs :>: pos)
  anfToplevel (TAssignment name expr :>: pos) = do
    (lets, expr') <- anfExpression expr
    return $ (lets, TAssignment name expr' :>: pos)
  anfToplevel (TConstant name expr :>: pos) = do
    (lets, expr') <- anfExpression expr
    return $ (lets, TConstant name expr' :>: pos)
  anfToplevel x = return ([], x)

  anfStatement :: MonadANF m => Located (Statement Type) -> m ([(Annoted String Type, Located (Expression Type))], Located (Statement Type))
  anfStatement (SAssignment name expr :>: pos) = do
    (lets, expr') <- anfExpression expr
    return $ (lets, SAssignment name expr' :>: pos)
  anfStatement (SIf cond then' else' :>: pos) = do
    (l1, cond') <- anfExpression cond
    (l2, then'') <- anfExpression then'
    else'' <- case else' of
      Nothing -> return Nothing
      Just x -> do
        x' <- anfExpression x
        return $ Just x'
    case else'' of
      Nothing -> return $ (l1 ++ l2, SIf cond' then'' Nothing :>: pos)
      Just (l3, else''') -> do
        let l = l1 ++ l2 ++ l3
        return $ (l, SIf cond' then'' (Just else''') :>: pos)
  anfStatement (SExpression expr :>: pos) = do
    (lets, expr') <- anfExpression expr
    return $ (lets, SExpression expr' :>: pos)
  anfStatement (SReturn expr :>: pos) = do
    (lets, expr') <- anfExpression expr
    return $ (lets, SReturn expr' :>: pos)
  anfStatement (SConstant name expr :>: pos) = do
    (lets, expr') <- anfExpression expr
    return $ (lets, SConstant name expr' :>: pos)
  anfStatement (SModified name expr :>: pos) = do
    (lets, expr') <- anfExpression expr
    return $ (lets, SModified name expr' :>: pos)

  anfExpression :: MonadANF m => Located (Expression Type) -> m ([(Annoted String Type, Located (Expression Type))], (Located (Expression Type)))
  anfExpression (EVariable n t c :>: pos) = ask >>= \env -> case lookup n env of
    Just n' -> return ([], EVariable n' t c :>: pos)
    Nothing -> return ([], EVariable n t c :>: pos)
  anfExpression (ECall func args t :>: pos) = do
    (l1, func') <- anfExpression func
    (l2s, args') <- unzip <$> mapM anfExpression args
    return $ (l1 ++ concat l2s, ECall func' args' t :>: pos)
  anfExpression (ETernary cond then' else' :>: pos) = do
    (l1, cond') <- anfExpression cond
    (l2, then'') <- anfExpression then'
    (l3, else'') <- anfExpression else'
    return $ (l1 ++ l2 ++ l3, ETernary cond' then'' else'' :>: pos)
  anfExpression (EBlock exprs :>: pos) = do
    (lets, exprs') <- unzip <$> mapM anfStatement exprs
    let lets' = map (\xs -> map (\(x, e@(_ :>: pos')) ->
            SAssignment x e :>: pos') xs) lets
    let xs = concatMap (\(lets'', x) -> lets'' ++ [x]) (zip lets' exprs')
    return $ ([], EBlock xs :>: pos)
  anfExpression (ELambda annots ret args body :>: pos) = do
    (l, body') <- anfExpression body
    return $ (l, ELambda annots ret args body' :>: pos)
  anfExpression (EUnaryOp op expr :>: pos) = do
    (l, expr') <- anfExpression expr
    return $ (l, EUnaryOp op expr' :>: pos)
  anfExpression (EBinaryOp op expr1 expr2 :>: pos) = do
    (l1, expr1') <- anfExpression expr1
    (l2, expr2') <- anfExpression expr2
    return $ (l1 ++ l2, EBinaryOp op expr1' expr2' :>: pos)
  anfExpression (EArrayAccess expr1 expr2 :>: pos) = do
    (l1, expr1') <- anfExpression expr1
    (l2, expr2') <- anfExpression expr2
    return $ (l1 ++ l2, EArrayAccess expr1' expr2' :>: pos)
  anfExpression (EArrayLiteral exprs :>: pos) = do
    (l, exprs') <- unzip <$> mapM anfExpression exprs
    return $ (concat l, EArrayLiteral exprs' :>: pos)
  anfExpression (EStructureLiteral fs :>: pos) = do
    (l, fs') <- unzip <$> mapM (\(name, expr) -> do
      (l, expr') <- anfExpression expr
      return $ (l, (name, expr'))) fs
    return $ (concat l, EStructureLiteral fs' :>: pos)
  anfExpression (EStructureAccess expr name :>: pos) = do
    (l, expr') <- anfExpression expr
    return $ (l, EStructureAccess expr' name :>: pos)
  anfExpression (ECast t expr :>: pos) = do
    (l, expr') <- anfExpression expr
    return $ (l, ECast t expr' :>: pos)
  anfExpression (EReference expr :>: pos) = do
    (l, expr') <- anfExpression expr
    return $ (l, EReference expr' :>: pos)
  anfExpression (EDereference expr :>: pos) = do
    (l, expr') <- anfExpression expr
    return $ (l, EDereference expr' :>: pos)
  anfExpression (ELetIn (n :@ t) expr body :>: _) = do
    name1 <- freshName
    (lets1, e') <- local (`union` [(n, name1)]) $ anfExpression expr
    (lets2, body') <- local (`union` [(n, name1)]) $ anfExpression body
    return (lets1 ++ [(name1 :@ t, e')] ++ lets2, body')
  anfExpression (ELiteral lit :>: pos) = return $ ([], ELiteral lit :>: pos)
  anfExpression (ESizeOf t :>: pos) = return $ ([], ESizeOf t :>: pos)

  runANF :: Monad m => [Located (Toplevel Type)] -> m [Located (Toplevel Type)]
  runANF xs = do
    (res, _, _) <- runRWST (mapM anfToplevel xs) [] 0
    let (lets, toplevels) = unzip res
    let lets' = map (\xs' -> map (\(x, e@(_ :>: pos')) ->
            TAssignment x e :>: pos') xs') lets
    let toplevels' = concatMap (\(lets'', x) -> lets'' ++ [x]) (zip lets' toplevels)
    return toplevels'