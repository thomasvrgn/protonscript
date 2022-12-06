{-# LANGUAGE LambdaCase #-}
module Core.Transformation.ClosureConversion where
  import qualified Data.Map as M
  import Core.Checker.Definition.Type
  import Control.Monad.RWS hiding (local)
  import Core.Parser.AST.Expression
  import Core.Parser.AST.Literal
  import Core.Transformation.Free
  import Core.Checker.Checker hiding (local, local')
  import Data.Tuple.Extra
  import Data.Maybe

  data ClosureState = ClosureState {
    counter :: Int,
    env :: M.Map String Type,
    mapping :: M.Map String String
  }
  type MonadClosure m = (MonadRWS () [Located (Toplevel Type)] ClosureState m, MonadFail m)

  fresh :: MonadClosure m => m String
  fresh = do
    s <- get
    let n = counter s
    put $ s { counter = counter s + 1 }
    return $ show n
  
  freshTy :: MonadClosure m => m Type
  freshTy = do
    s <- get
    let n = counter s
    put $ s { counter = counter s + 1 }
    return $ TVar n
  
  lookupEnv :: MonadClosure m => String -> m (Maybe Type)
  lookupEnv n = M.lookup n <$> gets env

  lookupMappings :: MonadClosure m => String -> m (Maybe String)
  lookupMappings n = M.lookup n <$> gets mapping

  addEnv :: MonadClosure m => String -> Type -> m ()
  addEnv n t = do
    s <- get
    put $ s { env = M.insert n t (env s) }
  
  local :: MonadState ClosureState m => (ClosureState -> ClosureState) -> m a -> m a
  local f m = do
    s <- get
    put $ f s
    a <- m
    counter <- gets counter
    put s
    modify $ \s' -> s' { counter = counter }
    return a
  
  local' :: MonadState ClosureState m => m a -> m a
  local' = local id
  
  convertTy :: MonadClosure m => String -> Type -> m Type
  convertTy n (args :-> ret) = do
    env <- freshTy
    args' <- mapM (convertTy "") args
    ret' <- convertTy "" ret
    let ty = TApp (TApp (TId "Closure") env) $ (env : args') :-> ret'
    addEnv n ty
    return ty
  convertTy _ (TApp n x) = do
    n' <- convertTy "" n
    x' <- convertTy "" x
    return $ TApp n' x'
  convertTy _ (TPtr t) = do
    t' <- convertTy "" t
    return $ TPtr t'
  convertTy _ (TRec fields) = do
    fields' <- mapM (traverse (convertTy "")) fields
    return $ TRec fields'
  convertTy _ x = return x

  convertToplevel :: MonadClosure m => Located (Toplevel Type) -> m (Located (Toplevel Type))  
  convertToplevel (TAssignment (name :@ _) (ELambda annots ret' args body :>: _) :>: pos) = do
    (body', _, _) <- local' $ convertExpr body
    return $ TFunction annots ret' name args [ SReturn body' :>: pos ] :>: pos
  convertToplevel (TAssignment (name :@ ret) expr :>: pos) = do
    (expr', _, _) <- local' $ convertExpr expr
    return $ TAssignment (name :@ ret) expr' :>: pos
  convertToplevel (TConstant (name :@ _) (ELambda annots ret' args body :>: _) :>: pos) = do
    (body', _, _) <- local' $ convertExpr body
    return $ TFunction annots ret' name args [ SReturn body' :>: pos ] :>: pos
  convertToplevel (TConstant (name :@ ret) expr :>: pos) = do
    (expr', _, _) <- local' $ convertExpr expr
    return $ TConstant (name :@ ret) expr' :>: pos
  convertToplevel (TFunction annots ret name args body :>: pos) = do
    (body', args') <- local' $ do
      a <- mapM (\(x :@ t) -> (x:@) <$> convertTy x t) args
      b <- mapM convertStmt body
      return (b, a)
    addEnv name $ map (snd . unannotate) args' :-> ret
    return $ TFunction annots ret name args' body' :>: pos
  convertToplevel x = return x

  convertStmt :: MonadClosure m => Located (Statement Type) -> m (Located (Statement Type))
  convertStmt (SReturn expr :>: pos) = do
    (expr', _, _) <- local' $ convertExpr expr
    return $ SReturn expr' :>: pos
  convertStmt (SExpression expr :>: pos) = do
    (expr', _, _) <- local' $ convertExpr expr
    return $ SExpression expr' :>: pos
  convertStmt (SIf cond then_ else_ :>: pos) = do
    (cond', _, _) <- local' $ convertExpr cond
    (then', _, _) <- local' $ convertExpr then_
    else' <- case else_ of
      Just e -> Just . fst3 <$> local' (convertExpr e)
      Nothing -> return Nothing
    return $ SIf cond' then' else' :>: pos
  convertStmt z@(SAssignment (name :@ _) (ELambda annots ret' args body :>: _) :>: pos) = do
    let env = free z
    (body', _, next) <- local' $ convertExpr body
    let structName = "$closure_" ++ name
    let envVar = EDereference (EVariable name (TId structName) [] :>: pos) :>: pos
    let envArg = (name :@ TPtr (TId structName))
    let ty = (fromMaybe ret' $ createRetType ret' <$> next)
    let funTy = (TPtr (TId structName) : map (snd . unannotate) args) :-> ty
    let struct = TStructure [] structName (map (uncurry (:@)) (M.toList env) ++ ["fun" :@ funTy]) :>: pos
    case next of
      Just (TId n) -> modify $ \s -> s { mapping = M.insert name n (mapping s) }
      _ -> return ()
    tell [struct]
    addEnv name (TId structName)
    let sequence' = M.mapWithKey (\k v -> SAssignment (k :@ v) (EStructureAccess envVar k :>: pos) :>: pos) env
    let body'' = case body' of
          EBlock stmts :>: pos' -> EBlock (map snd (M.toList sequence') ++ stmts) :>: pos'
          _ -> EBlock (map snd (M.toList sequence') ++ [SReturn body' :>: pos]) :>: pos
    return (SAssignment (name :@ createRetType ret' (TId structName)) (ECast (TId structName) (EStructureLiteral (("fun", ELambda annots ty (envArg:args) body'' :>: pos):map (\(x, t) -> (x, EVariable x t [] :>: pos)) (M.toList env)) :>: pos) :>: pos) :>: pos)
  convertStmt (SAssignment (name :@ ret) expr :>: pos) = do
    (expr', _, _) <- local' $ convertExpr expr
    return $ SAssignment (name :@ ret) expr' :>: pos
  convertStmt z@(SConstant (name :@ _) (ELambda annots ret' args body :>: _) :>: pos) = do
    let env = free z
    (body', _, next) <- local' $ convertExpr body
    let structName = "$closure_" ++ name
    let envVar = EDereference (EVariable name (TId structName) [] :>: pos) :>: pos
    let envArg = (name :@ TPtr (TId structName))
    let ty = (fromMaybe ret' $ createRetType ret' <$> next)
    let funTy = (TPtr (TId structName) : map (snd . unannotate) args) :-> ty
    let struct = TStructure [] structName (map (uncurry (:@)) (M.toList env) ++ ["fun" :@ funTy]) :>: pos
    let closureStruct = TApp (TApp (TId "closure") (TId name)) funTy
    
    case next of
      Just (TId n) -> modify $ \s -> s { mapping = M.insert name n (mapping s) }
      _ -> return ()
    tell [struct]
    addEnv name (TId structName)
    let sequence' = M.mapWithKey (\k v -> SAssignment (k :@ v) (EStructureAccess envVar k :>: pos) :>: pos) env
    let body'' = case body' of
          EBlock stmts :>: pos' -> EBlock (map snd (M.toList sequence') ++ stmts) :>: pos'
          _ -> EBlock (map snd (M.toList sequence') ++ [SReturn body' :>: pos]) :>: pos
    return (SConstant (name :@ createRetType ret' (TId structName)) (ECast closureStruct (EStructureLiteral (("fun", ELambda annots ty (envArg:args) body'' :>: pos):map (\(x, t) -> (x, EVariable x t [] :>: pos)) (M.toList env)) :>: pos) :>: pos) :>: pos)
  convertStmt (SConstant (name :@ ret) expr :>: pos) = do
    (expr', _, _) <- local' $ convertExpr expr
    return $ SConstant (name :@ ret) expr' :>: pos
  convertStmt (SModified n expr :>: pos) = do
    (expr', _, _) <- local' $ convertExpr expr
    return $ SModified n expr' :>: pos

  createRetType :: Type -> Type -> Type
  createRetType (_ :-> _) n = n
  createRetType t _ = t

  convertExpr :: MonadClosure m => Located (Expression Type) -> m (Located (Expression Type), Maybe Type, Maybe Type)
  convertExpr z@(ELambda annots ret args body :>: pos) = do
    let env = free z
    name <- ("$lam_"++) <$> fresh
    (body', _, next) <- local' $ convertExpr body
    let envVar = EDereference (EVariable name (TId name) [] :>: pos) :>: pos
    let envArg = (name :@ TPtr (TId name))
    let ty = (fromMaybe ret $ createRetType ret <$> next)
    let funTy = (TPtr (TId name) : map (snd . unannotate) args) :-> ty
    let struct = TStructure [] name (map (uncurry (:@)) (M.toList env) ++ ["fun" :@ funTy]) :>: pos

    let closureStruct = TApp (TApp (TId "Closure") (TId name)) funTy
    
    case next of
      Just (TId n) -> modify $ \s -> s { mapping = M.insert name n (mapping s) }
      _ -> return ()

    tell [struct]
    let sequence' = M.mapWithKey (\k v -> SAssignment (k :@ v) (EStructureAccess envVar k :>: pos) :>: pos) env
    let body'' = case body' of
          EBlock stmts :>: pos' -> EBlock (map snd (M.toList sequence') ++ stmts) :>: pos'
          _ -> EBlock (map snd (M.toList sequence') ++ [SReturn body' :>: pos]) :>: pos
    return (ECast closureStruct (EStructureLiteral (("fun", ELambda annots ty(envArg:args) body'' :>: pos):map (\(x, t) -> (x, EVariable x t [] :>: pos)) (M.toList env)) :>: pos) :>: pos, Just $ TId name, Just $ TId name)
    -- name' <- ("$f"++) <$> fresh
    -- return (ELetIn (name' :@ TId name) (ECast (TId name) (EStructureLiteral (("fun", ELambda annots ty (envArg:args) body'' :>: pos):map (\(x, t) -> (x, EVariable x t :>: pos)) (M.toList env)) :>: pos) :>: pos) (EVariable name' (TId name) :>: pos) :>: pos, Just name, Just name)

  convertExpr (ECall n args t' :>: pos) = do
    (n', m, next) <- convertExpr n
    (args', _, _) <- unzip3 <$> mapM convertExpr args
    case m of
      Just t -> do
        f <- ("$fun_"++) <$> fresh
        let envArg = EReference (EVariable f (t) [] :>: pos) :>: pos
        let f' = EStructureAccess (EVariable f (t) [] :>: pos) "fun" :>: pos
        return (ELetIn (f :@ t) n' (ECall f' (envArg:args') t' :>: pos) :>: pos, next, Nothing)
      Nothing -> return (ECall n' args' t' :>: pos, Nothing, Nothing)
  convertExpr (EVariable n t c :>: pos) = do
   ty <- convertTy "" t
   lookupEnv n >>= \case
    Just t' -> lookupMappings n >>= \case
        Just t'' -> return (EVariable n t' c :>: pos, Just t', Just $ TId t'')
        Nothing -> return (EVariable n t' c :>: pos, Just t', Nothing)
    _ -> return (EVariable n ty c :>: pos, Nothing, Nothing)
    
  convertExpr (ELiteral l :>: p) = return (ELiteral l :>: p, Nothing, Nothing)
  convertExpr (EArrayLiteral es :>: p) = do
    es' <- local' $ mapM convertExpr es
    return (EArrayLiteral (map fst3 es') :>: p, Nothing,Nothing)
  convertExpr (EArrayAccess e i :>: p) = do
    e' <- local' $ convertExpr e
    i' <- local' $ convertExpr i
    return (EArrayAccess (fst3 e') (fst3 i') :>: p, Nothing, Nothing)
  convertExpr (EStructureLiteral fs :>: p) = do
    fs' <- local' $ mapM (convertExpr . snd) fs
    return (EStructureLiteral (zip (map fst fs) (map fst3 fs')) :>: p, Nothing, Nothing)
  convertExpr (EStructureAccess e f :>: p) = do
    e' <- local' $ convertExpr e
    return (EStructureAccess (fst3 e') f :>: p, Nothing, Nothing)
  convertExpr (EUnaryOp op e :>: p) = do
    e' <- local' $ convertExpr e
    return (EUnaryOp op (fst3 e') :>: p, Nothing, Nothing)
  convertExpr (EBinaryOp op e1 e2 :>: p) = do
    e1' <- local' $ convertExpr e1
    e2' <- local' $ convertExpr e2
    return (EBinaryOp op (fst3 e1') (fst3 e2') :>: p, Nothing, Nothing)
  convertExpr (EReference e :>: p) = do
    e' <- local' $ convertExpr e
    return (EReference (fst3 e') :>: p, Nothing, Nothing)
  convertExpr (EDereference e :>: p) = do
    e' <- local' $ convertExpr e
    return (EDereference (fst3 e') :>: p, Nothing, Nothing)
  convertExpr (EBlock es :>: p) = do
    es' <- local' $ mapM convertStmt es
    return (EBlock es' :>: p, Nothing, Nothing)
  convertExpr (ECast t e :>: p) = do
    e' <- local' $ convertExpr e
    return (ECast t (fst3 e') :>: p, Nothing, Nothing)
  convertExpr (ETernary cond e1 e2 :>: p) = do
    cond' <- local' $ convertExpr cond
    e1' <- local' $ convertExpr e1
    e2' <- local' $ convertExpr e2
    return (ETernary (fst3 cond') (fst3 e1') (fst3 e2') :>: p, Nothing, Nothing)
  convertExpr (ELetIn name e1 e2 :>: p) = do
    e1' <- local' $ convertExpr e1
    e2' <- local' $ convertExpr e2
    return (ELetIn name (fst3 e1') (fst3 e2') :>: p, Nothing, Nothing)
  convertExpr (ESizeOf t :>: p) = return (ESizeOf t :>: p, Nothing, Nothing)

  runClosureConversion :: MonadFail m => [Located (Toplevel Type)] -> Int -> m ([Located (Toplevel Type)], [Located (Toplevel Type)])
  runClosureConversion toplevels c = do
    (toplevels', _, structs) <- runRWST (mapM convertToplevel toplevels) () (ClosureState c M.empty M.empty)
    return (structs, toplevels')