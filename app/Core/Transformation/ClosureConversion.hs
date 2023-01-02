{-# LANGUAGE LambdaCase #-}
module Core.Transformation.ClosureConversion where
  import qualified Data.Map as M
  import Core.Checker.Definition.Type
  import Control.Monad.RWS hiding (local)
  import Core.Parser.AST.Expression
  import Core.Parser.AST.Literal
  import Core.Transformation.Free
  import Core.Checker.Checker hiding (local, local')
  import Data.Maybe
  import Data.Tuple.Extra

  data ClosureState = ClosureState {
    counter :: Int,
    env :: M.Map String Type,
    mapping :: M.Map String Type,
    excluded :: [String]
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

  lookupMappings :: MonadClosure m => String -> m (Maybe Type)
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
    let ty = TApp (TApp (TId "Closure") env) $ (TPtr env : args') :-> ret'
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
  convertToplevel (TAssignment (name :@ _) (ELambda annots ret' args body _ :>: _) :>: pos) = do
    (body', _, _) <- local' $ convertExpr body
    modify $ \s -> s { excluded = name : excluded s }
    return $ TFunction annots ret' name args [ SReturn body' :>: pos ] :>: pos
  convertToplevel (TAssignment (name :@ ret) expr :>: pos) = do
    (expr', _, _) <- local' $ convertExpr expr
    modify $ \s -> s { excluded = name : excluded s }
    return $ TAssignment (name :@ ret) expr' :>: pos
  convertToplevel (TConstant (name :@ _) (ELambda annots ret' args body _ :>: _) :>: pos) = do
    (body', _, _) <- local' $ convertExpr body
    modify $ \s -> s { excluded = name : excluded s }
    return $ TFunction annots ret' name args [ SReturn body' :>: pos ] :>: pos
  convertToplevel (TConstant (name :@ ret) expr :>: pos) = do
    (expr', _, _) <- local' $ convertExpr expr
    modify $ \s -> s { excluded = name : excluded s }
    return $ TConstant (name :@ ret) expr' :>: pos
  convertToplevel (TFunction annots ret name args body :>: pos) = do
    (body', args') <- local' $ do
      a <- mapM (\(x :@ t) -> (x:@) <$> convertTy x t) args
      (b, _) <- unzip <$> mapM convertStmt body
      return (b, a)
    modify $ \s -> s { excluded = name : excluded s }
    -- addEnv name $ map (snd . unannotate) args' :-> ret
    return $ TFunction annots ret name args' body' :>: pos
  convertToplevel x = return x

  unzip4 :: [(a, b, c, d)] -> ([a], [b], [c], [d])
  unzip4 = foldr (\(a, b, c, d) (as, bs, cs, ds) -> (a:as, b:bs, c:cs, d:ds)) ([], [], [], [])

  closureConvert :: MonadClosure m 
    => (Annoted String Type -> Located (Expression Type) -> Statement Type)
    -> Annoted String Type
    -> Located (Expression Type)
    -> Position
    -> m (Located (Statement Type), Maybe Type)
  closureConvert fun (name :@ vTy) (ELambda annots ret' args body t :>: _) pos = do
    -- Getting all free variables in the function body except for the function name and
    -- the arguments.
    (body', _, next) <- local' $ convertExpr body
    excluded <- gets excluded
    let vars = free $ fun (name :@ vTy) (ELambda annots ret' args body' t :>: pos)
    let env = M.filterWithKey (\x _ -> x `notElem` excluded) $ vars
    env' <- M.fromList <$> mapM (\(x, t') -> lookupEnv x >>= \case
      Just t'' -> return (x, t'')
      Nothing -> return (x, t')) (M.toList env)

    -- Creating a new closure structure and the new function type : (env, ...args) => ret
    -- where ret is the final return type of the function or the next function closure structure
    let structName = "$closure_" ++ name
    let envArg = (name :@ TPtr (TId structName))
    let ty = (fromMaybe ret' $ createRetType ret' <$> next)
    let funTy = (TPtr (TId structName) : map (snd . unannotate) args) :-> ty
    let struct = TStructure [] structName (map (uncurry (:@)) (M.toList env') ++ ["fun" :@ funTy]) :>: pos

    let envTy = TApp (TApp (TId "Closure") (TId structName)) funTy
    -- Adding the next body closure type to the list of mappings
    case next of
      Just n -> modify $ \s -> s { mapping = M.insert name n (mapping s) }
      _ -> modify $ \s -> s { mapping = M.insert name envTy (mapping s) }

    -- Adding the closure structure to the writer
    tell [struct]
    
    -- Creating the final closure type and adding it to the environment
    addEnv name envTy

    -- Creating variable access to the closure structure
    let envVar = EDereference (EVariable name (TId structName) [] :>: pos) :>: pos
    let sequence' = M.mapWithKey (\k v -> SAssignment (k :@ v) (EStructureAccess envVar k :>: pos) :>: pos) env'

    let body'' = case body' of
          EBlock stmts :>: pos' -> EBlock (map snd (M.toList sequence') ++ stmts) :>: pos'
          _ -> EBlock (map snd (M.toList sequence') ++ [SReturn body' :>: pos]) :>: pos

    -- Creating the closure literal structure
    let envFields = [("fun", ELambda annots ty (envArg:args) body'' funTy :>: pos), ("env", ECast (TId structName) (EStructureLiteral (map (\(x, t') -> (x, EVariable x t' [] :>: pos)) (M.toList env')) :>: pos) :>: pos)]

    -- Creating the final closure structure
    return (fun (name :@ envTy) (ECast envTy (EStructureLiteral envFields :>: pos) :>: pos) :>: pos, Nothing)
  closureConvert _ _ _ _ = error "closureConvert: not a lambda"

  convertStmt :: MonadClosure m => Located (Statement Type) -> m (Located (Statement Type), Maybe Type)
  convertStmt (SReturn expr :>: pos) = do
    (expr', _, next) <- local' $ convertExpr expr
    return (SReturn expr' :>: pos, next)
  convertStmt (SExpression expr :>: pos) = do
    (expr', _, _) <- local' $ convertExpr expr
    return $ (SExpression expr' :>: pos, Nothing)
  convertStmt (SIf cond then_ else_ :>: pos) = do
    (cond', _, _) <- local' $ convertExpr cond
    (then', _, _) <- local' $ convertExpr then_
    else' <- case else_ of
      Just e -> Just . fst3 <$> local' (convertExpr e)
      Nothing -> return Nothing
    return $ (SIf cond' then' else' :>: pos, Nothing)
  convertStmt (SAssignment (name :@ _) (EVariable n t c :>: p1) :>: p2) = do
    lookupEnv n >>= \case
      Just t' -> do
        addEnv name t'
        m <- lookupMappings n
        unless (isNothing m) $ 
          modify $ \s -> s { mapping = M.insert name (fromJust m) (mapping s) }
        return $ (SAssignment (name :@ t') (EVariable n t' c :>: p1) :>: p2, Nothing)
      Nothing -> do
        t' <- convertTy name t
        return $ (SAssignment (name :@ t') (EVariable n t c :>: p1) :>: p2, Nothing)
  convertStmt (SAssignment (name :@ vTy) (ELambda annots ret' args body t :>: p1) :>: pos) = do
    closureConvert SAssignment (name :@ vTy) (ELambda annots ret' args body t :>: p1) pos
  convertStmt (SAssignment (name :@ ret) expr :>: pos) = do
    (expr', funTy, _) <- local' $ convertExpr expr

    case expr' of
      ELetIn (name' :@ t) expr'' body :>: pos' -> do
        addEnv name (fromMaybe ret funTy)
        case ret of
          _ :-> _ -> do
            return $ (SAssignment (name :@ fromMaybe ret funTy) (ELetIn (name' :@ t) expr'' body :>: pos') :>: pos, Nothing)
          _ -> do
            return $ (SAssignment (name :@ ret) (ELetIn (name' :@ t) expr'' body :>: pos') :>: pos, Nothing)
      _ -> return $ (SAssignment (name :@ ret) expr' :>: pos, Nothing)
  convertStmt (SConstant (name :@ _) (EVariable n t c :>: p1) :>: p2) = do
    lookupEnv n >>= \case
      Just t' -> do
        addEnv name t'
        return $ (SConstant (name :@ t') (EVariable n t' c :>: p1) :>: p2, Nothing)
      Nothing -> do
        t' <- convertTy name t
        return $ (SConstant (name :@ t') (EVariable n t c :>: p1) :>: p2, Nothing)
  convertStmt (SConstant (name :@ vTy) (ELambda annots ret' args body t :>: p1) :>: pos) =  do
    closureConvert SConstant (name :@ vTy) (ELambda annots ret' args body t :>: p1) pos
  convertStmt (SConstant (name :@ ret) expr :>: pos) = do
    (expr', _, _) <- local' $ convertExpr expr
    return $ (SConstant (name :@ ret) expr' :>: pos, Nothing)
  convertStmt (SModified n expr :>: pos) = do
    (expr', _, _) <- local' $ convertExpr expr
    return $ (SModified n expr' :>: pos, Nothing)

  createRetType :: Type -> Type -> Type
  createRetType (_ :-> _) n = n
  createRetType t _ = t

  convertExpr :: MonadClosure m => Located (Expression Type) -> m (Located (Expression Type), Maybe Type, Maybe Type)
  convertExpr (ELambda _ _ _ _ _ :>: _) = error "Should not happen"
  convertExpr (ECall v@(EVariable n (argsTy :-> ret) c :>: p1) args t' :>: p2) = do
    (v', funTy, next) <- local' $ convertExpr v
    args' <- unzip3 <$> local' (mapM convertExpr args)
    case funTy of
      Nothing -> do
        let argsTy' = zipWith (\x y -> fromMaybe x y) (argsTy) (snd3 args')
        let ty = argsTy' :-> ret
        return (ECall (EVariable n ty c :>: p1) (fst3 args') t' :>: p2, next, Nothing)
      Just t -> do
        f <- ("$fun_"++) <$> fresh
        let envArg = EReference (EVariable f t [] :>: p1) :>: p1
        let f' = EStructureAccess (EVariable f t [] :>: p1) "fun" :>: p1
        return (ELetIn (f :@ t) v' (ECall f' (envArg:fst3 args') t' :>: p2) :>: p2, next, Nothing)
  convertExpr (ECall _ _ _ :>: _) = error "Should not happen"
  convertExpr (EVariable n t c :>: pos) = do
    funTy <- lookupEnv n
    next <- lookupMappings n
    return (EVariable n t c :>: pos, funTy, next)
  convertExpr (ELiteral l :>: p) = return (ELiteral l :>: p, Nothing, Nothing)
  convertExpr (EArrayLiteral es :>: p) = do
    es' <- local' $ mapM convertExpr es
    return (EArrayLiteral (map fst3 es') :>: p, Nothing, Nothing)
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
    (es', nexts) <- unzip <$> local' (mapM convertStmt es)
    return (EBlock es' :>: p, Nothing, last nexts)
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

  createType :: [Type] -> [Maybe Type] -> [Type]
  createType (t:ts) (Nothing:ms) = t : createType ts ms
  createType (t:ts) (Just m:ms) = (TApp (TApp (TId "Closure") m) t) : createType ts ms
  createType [] [] = []
  createType _ _ = error "createType: invalid arguments"


  runClosureConversion :: MonadFail m => [Located (Toplevel Type)] -> Int -> m ([Located (Toplevel Type)], [Located (Toplevel Type)])
  runClosureConversion toplevels c = do
    (toplevels', _, structs) <- runRWST (mapM convertToplevel toplevels) () (ClosureState c M.empty M.empty ["printf"])
    return (structs, toplevels')