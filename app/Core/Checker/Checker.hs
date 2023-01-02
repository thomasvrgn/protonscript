{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Core.Checker.Checker where
  import Control.Monad.RWS hiding (local)
  import qualified Control.Monad.RWS as RWS
  import Control.Monad.Except
  import Core.Parser.AST.Expression
  import Core.Parser.AST.Literal
  import Core.Checker.Definition.Type
  import Core.Checker.Definition.Methods
  import qualified Data.Set as S
  import qualified Data.Map as M
  import Core.Checker.Substitution (Types(free, apply), Substitution)
  import Core.Checker.Unification
  import Data.List (unzip4)
  import qualified Data.Bifunctor as B
  import Data.Foldable.Extra (foldlM)
  import Data.Maybe
  import System.FilePath
  import System.Directory
  import Core.Parser.Parser hiding (buildFun)
  import Core.Error
  import System.Exit

  generalize :: Env -> Bool -> Bool -> Type -> Scheme
  generalize (env, _) m p t = Forall m p (map read $ S.toList vars) t
    where vars = free t S.\\ free env

  unannotate :: Annoted a b -> (a, b)
  unannotate (x :@ t) = (x, t)

  local :: MonadType m => (Env -> Env) -> m a -> m a
  local f m = do
    env <- gets env
    modify $ \c -> c { env = f env }
    a <- m
    modify $ \c -> c { env = env }
    return a
  
  local' :: MonadType m => m a -> m a
  local' = local id

  type Infer f m = MonadType m => Located (f (Maybe Declaration)) -> m (Type, Substitution, Located (f Type))

  fromDeclaration :: MonadType m => M.Map String Type -> Declaration -> m Type
  fromDeclaration m = \case
    DId n -> case M.lookup n m of
      Just t -> return t
      Nothing -> return $ TId n
    DPointer t -> TPtr <$> (fromDeclaration m t)
    DApp (DId "Ref") t -> TPtr <$> (fromDeclaration m t)
    DFunction annots ret args -> do
      annots' <- mapM (const fresh) annots
      let map' = M.fromList $ zip annots annots'
      let m' = M.union map' m
      (:->) <$> mapM (fromDeclaration m') args <*> fromDeclaration m' ret 
    DVoid -> return Void
    DApp t arg -> TApp <$> fromDeclaration m t <*> fromDeclaration m arg
    DChar -> return Char
    DInt -> return Int
    DFloat -> return Float
    DCast _ -> return Void

  applyForall :: Substitution -> Scheme -> Scheme
  applyForall s (Forall m p tvs t) = Forall m p tvs $ apply s t
  
  inferE :: Infer Expression m
  inferE (EVariable n _ casts :>: pos) = do
    (env, c) <- gets env
    case M.lookup n env of
      Nothing -> throwError ("Variable " ++ n ++ " not found", Nothing, pos)
      Just t@(Forall _ _ tvs t') -> do
        map' <- ask
        let cast = catMaybes casts
        cast' <- mapM (map' `fromDeclaration`) cast
        let s = M.fromList $ zip tvs cast'
        t'' <- tyInstantiate (applyForall s t)
        s' <- mgu c t' t''
        case s' of
          Right s'' -> return (t'', M.empty, EVariable n t'' (M.elems s'') :>: pos)
          Left err -> throwError (err, Nothing, pos)
  inferE (EStructureLiteral fields :>: pos) = do
    fields' <- mapM (\(n, e) -> do
      (t, s, e') <- local' $ inferE e
      return (n, t, s, e')) fields
    let (names, types, subs, exprs) = unzip4 fields'
    let t = TRec $ zip names types
    let s = foldl compose M.empty subs
    let t' = apply s t
    let exprs' = map (apply s) exprs
    return (t', s, EStructureLiteral (zip names exprs') :>: pos)
  inferE (EArrayLiteral exprs :>: pos) = do
    exprs' <- mapM (local' . inferE) exprs
    let (types, subs, exprs'') = unzip3 exprs'
    let t = TPtr $ head types
    let s = foldl compose M.empty subs
    let t' = apply s t
    let exprs''' = map (apply s) exprs''
    return (t', s, EArrayLiteral exprs''' :>: pos)
  inferE (ECall n xs _ :>: pos) = do
    tv <- fresh
    (t1, s1, n1) <- local' $ inferE n
    (t2, s2, args) <- foldlM (\(t, s, a) x -> do
      (t', s', a') <- local (apply s) $ inferE x
      return (t ++ [t'], s' `compose` s, a ++ [a'])) ([], s1, []) xs
    (_, c) <- gets env
    
    s'' <- mgu c (t2 :-> tv) (apply s2 t1)
    case s'' of
      Right s3 -> do
        return (apply s3 tv, s3 `compose` s2 `compose` s1, apply s3 $ ECall n1 args (apply s3 tv) :>: pos)
      Left x -> throwError (x, Nothing, pos)
  inferE (ELambda annots ret args e _ :>: pos) = do
    annots' <- mapM (const fresh) annots
    let map' = M.fromList $ zip annots annots'
    ret' <- case ret of
      Just t -> fromDeclaration map' t
      Nothing -> fresh
    args' <- mapM (\(x :@ t) -> (x,) <$> (case t of
      Just t' -> fromDeclaration map' t'
      Nothing -> fresh)) args
    (env, c) <- gets env
    let env'  = foldl (flip M.delete) env $ map fst args'
        env'' = env' `M.union` M.fromList (zipWith (\x t -> (x, Forall False False [] t)) (map fst args') (map snd args'))
    (t, s, e') <- RWS.local (`M.union` map') $ local (B.first $ M.union env'') $ inferE e
    mgu c ret' t >>= \case
      Right s' -> do
        let s'' = s' `compose` s
        return (apply s'' $ map snd args' :-> apply s'' ret', s'', ELambda annots ret' (zipWith (:@) (map fst args') (apply s'' $ map snd args')) (apply s'' (createCastReturn' ret' e')) (apply s'' $ map snd args' :-> apply s'' ret') :>: pos)
      Left x -> throwError (x, Nothing, pos)
  inferE (ELiteral l :>: pos) = do
    t <- case l of
      IntLit _ -> return Int
      FloatLit _ -> return Float
      CharLit _ -> return Char
      StringLit _ -> return $ TPtr Char
    return (t, M.empty, ELiteral l :>: pos)
  inferE (EBinaryOp op e1 e2 :>: pos) = do
    (t1, s1, v1) <- local' $ inferE (ECall (EVariable op Nothing [] :>: pos) [e1, e2] Nothing :>: pos)
    case v1 of
      ECall (EVariable op' _ _ :>: _) [e1', e2'] _ :>: pos' ->
        return (t1, s1, EBinaryOp op' e1' e2' :>: pos')
      _ -> throwError ("Error that should not happen", Nothing, pos)
  inferE (EUnaryOp op e :>: pos) = do
    (t1, s1, v1) <- local' $ inferE (ECall (EVariable op Nothing [] :>: pos) [e] Nothing :>: pos)
    case v1 of
      ECall (EVariable op' _ _ :>: _) [e'] _ :>: pos' ->
        return (t1, s1, EUnaryOp op' e' :>: pos')
      _ -> throwError ("Error that should not happen", Nothing, pos)
  inferE (ECast t e :>: pos) = do
    (t1, s1, v1) <- local' $ inferE e
    map' <- ask
    t' <- case t of
      Just t' -> fromDeclaration map' t'
      Nothing -> throwError ("Type annotation missing", Nothing, pos)
    (_, c) <- gets env
    mgu c t' t1 >>= \case
      Right s2 -> do
        return (t', s2 `compose` s1, ECast t' v1 :>: pos)
      Left x -> throwError (x, Nothing, pos)
  inferE (ETernary e1 e2 e3 :>: pos) = do
    (t1, s1, v1) <- local' $ inferE e1
    (t2, s2, v2) <- local (apply s1) $ inferE e2
    (t3, s3, v3) <- local (apply s2) $ inferE e3
    (_, c) <- gets env
    mgu c t1 Bool >>= \case
      Right s4 -> do
        mgu c (apply s4 t2) (apply s4 t3) >>= \case
          Right s5 -> do
            return (apply s5 t2, s5 `compose` s4 `compose` s3 `compose` s2 `compose` s1, ETernary v1 v2 v3 :>: pos)
          Left x -> throwError (x, Nothing, pos)
      Left x -> throwError (x, Nothing, pos)
  inferE (EStructureAccess e n :>: pos) = do
    (t1, s1, v1) <- local' $ inferE e
    tv <- fresh
    (_, c) <- gets env
    t' <- lookupCons t1 >>= \case
      Just (_, scheme) -> tyInstantiate scheme >>= \case
        ([t''] :-> header) -> case t'' of
          TRec fields -> case lookup n fields of
            Just _ -> do
              s <- mgu c t1 header
              case s of
                Right s' -> return $ apply s' t''
                Left x -> throwError (x, Nothing, pos)
            Nothing -> throwError (
              "Property " ++ n ++ " of type " ++ n ++ " is undefined",
              Just "Check that the property exists in the class and the typos", pos)
          _ -> throwError ("Expected structure, received " ++ show t'', Nothing, pos)
        _ -> throwError ("Error that should not happen", Nothing, pos)
      Nothing -> throwError (n ++ " is not declared", Nothing, pos)
    s2 <- mgu c (case t' of
      [ty] :-> _ -> ty
      _ -> t') (TRec [(n, tv)])
    let s3 = compose <$> s2 <*> pure s1
    case s3 of
      Right s -> do
        return (apply s tv, s, EStructureAccess v1 n :>: pos)
      Left x -> throwError (x, Nothing, pos)
  inferE (EArrayAccess e1 e2 :>: pos) = do
    (t1, s1, v1) <- local' $ inferE e1
    (t2, s2, v2) <- local (apply s1) $ inferE e2
    (_, c) <- gets env
    mgu c t2 Int >>= \case
      Right s3 -> do
        tv <- fresh
        mgu c (apply s3 t1) (TPtr tv) >>= \case
          Right s4 -> do
            let s5 = s4 `compose` s3 `compose` s2 `compose` s1
            return (apply s5 tv, s5, EArrayAccess v1 v2 :>: pos)
          _ -> throwError ("Not an array", Nothing, pos)
      Left x -> throwError (x, Nothing, pos)
  inferE (EReference e :>: pos) = do
    (t1, s1, v1) <- local' $ inferE e
    return (TPtr t1, s1, EReference v1 :>: pos)
  inferE (EDereference e :>: pos) = do
    ty <- fresh
    (t, s, n1) <- local' $ inferE e
    (_, c) <- gets env
    mgu c t (TPtr ty) >>= \case
      Right s' -> do
        let s2 = s' `compose` s
        return (apply s2 ty, s2, EDereference n1 :>: pos)
      Left x -> throwError (x, Nothing, pos)
  inferE (EBlock es :>: pos) = do
    (ts, s, es') <- unzip3 <$> (local' $ mapM inferS es)
    return (last ts, foldl compose M.empty s, EBlock es' :>: pos)
  inferE (ELetIn _ _ _ :>: pos) = throwError ("Let-in not supported", Nothing, pos)
  inferE (ESizeOf e :>: pos) = do
    env <- ask
    e' <- case e of
      Just e' -> return e'
      Nothing -> throwError ("Type annotation missing", Nothing, pos)
    t <- fromDeclaration env e'
    return (Int, M.empty, ESizeOf t :>: pos)

  inferVariable :: MonadType m => Bool -> Bool -> String -> Maybe Declaration -> Located (Expression (Maybe Declaration)) -> Position -> m (Type, Substitution, Annoted String Type, Located (Expression Type))
  inferVariable isMutable public name ty value pos = do
    -- Fresh type for recursive definitions
    map' <- ask
    e@(env', cons) <- gets env
    (tv, e') <- case ty of
      Just t -> do
        t' <- generalize e False public <$> fromDeclaration map' t 
        t'' <- tyInstantiate t'
        return (t'', M.singleton name (Forall False public [] t''))
      Nothing -> do
        tv <- fresh
        return (tv, M.singleton name (Forall False public [] tv))
    (t1, s1, v1) <- local (B.first (`M.union` e')) $ inferE value

    s' <- mgu cons (apply s1 tv) t1 >>= \case
      Right s2 -> do
        let s3 = s2 `compose` s1
        return s3
      Left x -> throwError (x, Nothing, pos)

    let env''  = M.delete name env'
        t'     = Forall isMutable public [] (apply s' tv)
        env''' = M.insert name t' env''
    modify $ \env -> env { env = (env''', cons) }
    return (Void, s', (name :@ apply s' tv), (apply s' v1))

  buildFun :: [Type] -> Type -> Type
  buildFun xs t = go (reverse xs) t
    where go [] t' = t'
          go (x:xs') t' = TApp (go xs' t') x

  createCastReturn :: Type -> [Located (Statement Type)] -> [Located (Statement Type)]
  createCastReturn t xs
    | length xs > 0 = map (\x -> case x of
        (SReturn e@(EStructureLiteral _ :>: _) :>: p2) -> SReturn (ECast t e :>: p2) :>: p2
        (SIf e s1 s2 :>: p2) -> SIf e (createCastReturn' t s1) (createCastReturn' t <$> s2) :>: p2
        _ -> x) xs
    | otherwise = xs

  createCastReturn' :: Type -> Located (Expression Type) -> Located (Expression Type)
  createCastReturn' t xs = case xs of
    (EStructureLiteral fs :>: p1) -> ECast t (EStructureLiteral fs :>: p1) :>: p1
    (EBlock xs' :>: p1) -> EBlock (createCastReturn t xs') :>: p1
    _ -> xs

  extractType :: Type -> String
  extractType (TApp t1 _) = extractType t1
  extractType (TId t) = t
  extractType _ = ""

  inferT :: MonadType m => (String, Bool) -> Located (Toplevel (Maybe Declaration)) -> m (Type, Substitution, Located (Toplevel Type))
  inferT (_, p) (TAssignment (name :@ ty) value :>: pos) = do
    (t, s, n, v) <- inferVariable True p name ty value pos
    return (t, s, TAssignment n v :>: pos)
  inferT (_, p) (TFunction annot ret name args body :>: pos) = do
    annot' <- mapM (const fresh) annot
    let map' = M.fromList $ zip annot annot'
    ret' <- case ret of
      Just t -> fromDeclaration map' t
      Nothing -> fresh
    args' <- mapM (\(x :@ t) -> (x,) <$> (case t of
      Just t' -> fromDeclaration map' t'
      Nothing -> fresh)) args
    (env', c) <- gets env
    let env1  = foldl (flip M.delete) env' $ map fst args'
        env2 = env1 `M.union` M.fromList (zipWith (\x t -> (x, Forall False False [] t)) (map fst args') (map snd args')) `M.union` M.singleton name (Forall False p [] ((map snd args') :-> ret'))
    (t, s, body') <- unzip3 <$> (RWS.local (`M.union` map') $ local (B.first $ M.union env2) $ mapM inferS body)
    let s' = foldl compose M.empty s
    let retT = case t of
          [] -> Void
          _ -> last t
    mgu c retT ret' >>= \case
      Right s'' -> do
        let s''' = s'' `compose` s'
        let ret'' = apply s''' ret'
        let env1'  = M.delete name env1
            t'    = case apply s''' ret'' of
                  TPtr _ -> Forall False p [] (apply s''' $ map snd args' :-> ret'')
                  _ -> generalize (applyEnv s''' (env1', c)) False p (apply s''' $ map snd args' :-> ret'')
            env2' = M.insert name t' env1'
        modify $ \env -> env { env = (env2', c) }
        return (Void, s''', apply s''' $ TFunction annot ret'' name (zipWith (:@) (map fst args') (apply s''' $ map snd args')) (createCastReturn ret'' body') :>: pos)
      Left x -> throwError (x, Nothing, pos)
  inferT (_, p) (TConstant (name :@ ty) value :>: pos) = do
    (t, s, n, v) <- inferVariable False p name ty value pos
    return (t, s, TConstant n v :>: pos)
  inferT (_, p) (TDeclaration (name :@ t) :>: pos) = case t of
    Nothing -> throwError ("No type for declaration", Nothing, pos)
    Just t' -> do
      e@(env', c) <- gets env
      t1 <- generalize e False p <$> fromDeclaration M.empty t'
      t2 <- tyInstantiate t1
      modify $ \env -> env { env = (M.insert name t1 env', c) }
      return (Void, M.empty, TDeclaration (name :@ t2) :>: pos)
  inferT (_, p) (TEnumeration name fields :>: pos) = do
    (env', c) <- gets env
    let header = TId name
    let c' = M.union c $ M.fromList $ map (\x -> (TId x, Forall False p [] header)) fields
    modify $ \env -> env { env = (env', c') }
    return (Void, M.empty, TEnumeration name fields :>: pos)
  inferT (_, p) (TStructure gen name fields :>: pos) = do
    e@(env', c) <- gets env
    generic <- mapM (const fresh) gen
    -- Recreating a map mapping generic name to type
    let table = M.fromList (zip (map (maybe (error "test") (\(DId x) -> x)) gen) generic)
    gens <- mapM (fromDeclaration table . fromMaybe (error "tset")) gen
    let header = if null table then TId name else buildFun (M.elems table) (TId name)
    fields' <- mapM (\(x :@ t) -> 
      (x,) <$> fromDeclaration table (fromMaybe DVoid t)) fields
    let rec = [TRec fields'] :-> header
    let fields'' = generalize e False p rec
    let c' = M.union c $ M.singleton header fields''
    modify $ \env -> env { env = (env', c') }
    return (Void, M.empty, TStructure gens name (map (uncurry (:@)) fields') :>: pos)
  inferT (dir, _) (TExport el :>: _) = inferT (dir, True) el
  inferT (dir, _) (TImport meta path :>: pos) = do
    let path' = dir </> path -<.> "ts"
    liftIO (doesFileExist path') >>= \case
      False -> throwError ("File " ++ path' ++ " not found", Nothing, pos)
      True -> do
        content <- liftIO $ readFile path'
        (env', c) <- gets env
        let ast = parseProton path' content
        case ast of
          Left err -> liftIO $ printParseError err path' >> exitFailure
          Right ast' -> do
            xs <- runInfer (takeDirectory path', False) ast'
            case xs of
              Left err -> throwError err
              Right (TypeState _ _ (env2, c'), xs') -> do
                let (env3, c2) = case meta of
                      INone -> (filterEnvIsPublic env2, filterEnvIsPublic c')
                      IOnly funs -> 
                        (M.filterWithKey (\k _ -> k `elem` funs) $ filterEnvIsPublic env2, M.filterWithKey (\k _ -> extractType k `elem` funs) $ filterEnvIsPublic c')
                      _ -> error "Not implemented yet"
                
                case meta of
                  IOnly funs -> do
                    forM_ funs $ \f -> do
                      let t = M.lookup f env2
                      case t of
                        Nothing -> if length (M.filterWithKey (\k _ -> extractType k `elem` funs) c2) == 0
                          then throwError ("Function " ++ f ++ " not found in " ++ path', Nothing, pos)
                          else return ()
                        Just _ -> return ()
                  _ -> return ()

                let env4 = M.union env' env3
                let c3 = M.union c c2
                modify $ \env -> env { env = (env4, c3), modules = M.insert path' (Module path' xs') (modules env) }
                return (Void, M.empty, TImport meta path :>: pos)
  inferT _ (TType _ _ :>: pos) = throwError ("Type aliasing is not supported", Nothing, pos)
  inferT _ (_ :>: pos) = throwError ("Not implemented yet", Nothing, pos)

  filterEnvIsPublic :: M.Map a Scheme -> M.Map a Scheme
  filterEnvIsPublic = M.map (\(Forall m _ tvs t) -> Forall m False tvs t) . M.filter (\(Forall _ t _ _) -> t)

  getModifiedType :: MonadType m => Located (Expression (Maybe Declaration)) -> m (String, Type)
  getModifiedType (EArrayAccess e _ :>: _) = getModifiedType e
  getModifiedType (EStructureAccess e _ :>: _) = getModifiedType e
  getModifiedType (EDereference e :>: _) = getModifiedType e
  getModifiedType (EVariable x _ _ :>: pos) = do
    (env, _) <- gets env
    case M.lookup x env of
      Just (Forall _ _ _ t) -> return (x, t)
      Nothing -> throwError ("Variable " ++ x ++ " not found", Nothing, pos)
  getModifiedType (_ :>: pos) = throwError ("Invalid expression", Nothing, pos)

  inferModified :: MonadType m => Located (Expression (Maybe Declaration)) -> m (Type, Substitution, Located (Expression Type), Type)
  inferModified (EArrayAccess e i :>: pos) = do
    (t, s, e', _) <- local' $ inferModified e
    (t', s', i') <- local' $ inferE i
    (_, c) <- gets env
    mgu c t' Int >>= \case
      Right s3 -> do
        tv <- fresh
        mgu c (apply s3 t) (TPtr tv) >>= \case
          Right s4 -> do
            let s5 = s4 `compose` s3 `compose` s `compose` s'
            return (apply s5 tv, s5, EArrayAccess (apply s5 e') (apply s5 i') :>: pos, apply s5 tv)
          Left x -> throwError (x, Nothing, pos)
      Left x -> throwError (x, Nothing, pos)
  inferModified (EStructureAccess e n :>: pos) = do
    (t1, s1, v1, _) <- local' $ inferModified e
    tv <- fresh
    (_, c) <- gets env
    (t', h) <- lookupCons t1 >>= \case
      Just (_, scheme) -> tyInstantiate scheme >>= \case
        ([t''] :-> header) -> case t'' of
          TRec fields -> case lookup n fields of
            Just _ -> do
              s <- mgu c t1 header
              case s of
                Right s' -> return $ (apply s' t'', apply s' t1)
                Left x -> throwError (x, Nothing, pos)
            Nothing -> throwError (
              "Property " ++ n ++ " of type " ++ n ++ " is undefined",
              Just "Check that the property exists in the class and the typos", pos)
          _ -> throwError ("Expected structure, received " ++ show t'', Nothing, pos)
        _ -> throwError ("Error that should not happen", Nothing, pos)
      Nothing -> throwError ("Expected a structure, received " ++ show t1, Nothing, pos)
    s2 <- mgu c (case t' of
      [ty] :-> _ -> ty
      _ -> t') (TRec [(n, tv)])
    let s3 = compose <$> s2 <*> pure s1
    case s3 of
      Right s -> do
        return (apply s tv, s, EStructureAccess v1 n :>: pos, apply s h)
      Left x -> throwError (x, Nothing, pos)
  inferModified (EDereference e :>: pos) = do
    (t, s, e', _) <- local' $ inferModified e
    tv <- fresh
    (_, c) <- gets env
    mgu c t (TPtr tv) >>= \case
      Right s' -> do
        let s'' = s' `compose` s
        return (apply s'' tv, s'', EDereference (apply s'' e') :>: pos, apply s'' tv)
      Left x -> throwError (x, Nothing, pos)
  inferModified (EVariable n _ _ :>: pos) = do
    (env, _) <- gets env
    case M.lookup n env of
      Nothing -> throwError ("Variable " ++ n ++ " not found", Nothing, pos)
      Just (Forall mut _ _ t) -> do
        if mut 
          then return (t, M.empty, EVariable n t [] :>: pos, t)
          else
            throwError ("Variable " ++ n ++ " is not mutable", Nothing, pos)
  inferModified (_ :>: pos) = throwError ("Expected a mutable expression", Nothing, pos)

  inferS :: Infer Statement m
  inferS (SReturn e :>: pos) = do
    (t, s, e') <- local' $ inferE e
    return (t, s, SReturn e' :>: pos)
  inferS (SAssignment n e :>: pos) = do
    inferT ("", False) (TAssignment n e :>: pos) >>= \case
      (Void, s, TAssignment n' e' :>: pos') -> return (Void, s, SAssignment n' e' :>: pos')
      _ -> throwError ("Error that should not happen", Nothing, pos)
  inferS (SModified n expr :>: pos) = do
    (t, s, n', _) <- local' $ inferModified n
    (name, tn') <- getModifiedType n
    (t', s1, expr') <- local' $ inferE expr
    (_, c) <- gets env
    s2 <- mgu c t t'
    case s2 of
      Right s3 -> do
        let s4 = s3 `compose` s1 `compose` s
        (env', _) <- gets env
        let env'' = M.insert name (Forall True False [] $ apply s4 tn') env'
        modify $ \env -> env { env = (env'', c) }
        return (Void, s4, SModified n' (ECast t expr' :>: pos) :>: pos)
      Left x -> throwError (x, Nothing, pos)
  inferS (SConstant n e :>: pos) = 
    inferT ("", False) (TConstant n e :>: pos) >>= \case
      (Void, s, TConstant n' e' :>: pos') -> return (Void, s, SConstant n' e' :>: pos')
      _ -> throwError ("Error that should not happen", Nothing, pos)
  inferS (SExpression e :>: pos) = do
    (_, s, e') <- local' $ inferE e
    return (Void, s, SExpression e' :>: pos)
  inferS (SIf e s1 s2 :>: pos) = do
    (t, s, e') <- local' $ inferE e
    (t1, s1', s1'') <- local (B.first $ apply s) $ inferE s1
    (t2, s2', s2'') <- local (B.first $ apply s1') (case s2 of
      Just s2' -> do
        (t2, s2'', e2) <- local' $ inferE s2'
        return (Just t2, s2'', Just e2)
      Nothing -> return (Nothing, M.empty, Nothing))
    (_, c) <- gets env
    mgu c t Bool >>= \case
      Right s3 -> do
        let s4 = s3 `compose` s2' `compose` s1' `compose` s
        (case t2 of
          Just t3 -> Just <$> mgu c t1 t3
          Nothing -> return Nothing) >>= \case
          Nothing -> return (t1, s4, SIf e' s1'' s2'' :>: pos)
          Just (Right s5) -> do
            let s6 = s5 `compose` s4
            return (apply s6 t1, s6, SIf e' s1'' s2'' :>: pos)
          Just (Left x) -> throwError (x, Nothing, pos)
      Left x -> throwError (x, Nothing, pos)

  functions :: TypeEnv
  functions = M.fromList [
      ("+", Forall False True [0] $ [TVar 0, TVar 0] :-> TVar 0),
      ("null", Forall False True [0] $ TPtr (TVar 0)),
      ("printf", Forall False True [0] $ [TPtr Char, TVar 0] :-> Int),
      ("==", Forall False True [0] $ [TVar 0, TVar 0] :-> Bool),
      ("!=", Forall False True [0] $ [TVar 0, TVar 0] :-> Bool),
      ("&&", Forall False True [] $ [Bool, Bool] :-> Bool),
      ("||", Forall False True [] $ [Bool, Bool] :-> Bool),
      ("!", Forall False True [] $ [Bool] :-> Bool),
      ("*", Forall False True [0] $ [TVar 0, TVar 0] :-> TVar 0),
      ("-", Forall False True [0] $ [TVar 0, TVar 0] :-> TVar 0),
      ("^", Forall False True [0] $ [TVar 0, TVar 0] :-> TVar 0),
      ("&", Forall False True [0] $ [TVar 0, TVar 0] :-> TVar 0),
      ("|", Forall False True [0] $ [TVar 0, TVar 0] :-> TVar 0),
      ("<<", Forall False True [0] $ [TVar 0, TVar 0] :-> TVar 0),
      (">>", Forall False True [0] $ [TVar 0, TVar 0] :-> TVar 0),
      ("~", Forall False True [0] $ [TVar 0] :-> TVar 0)
    ]

  runInfer :: MonadIO m => (String, Bool) -> [Located (Toplevel (Maybe Declaration))] -> m (Either (String, Maybe String, Position) (TypeState, [Located (Toplevel Type)]))
  runInfer isImport xs = do
    x <- runExceptT $ runRWST (mapM (inferT isImport) xs) M.empty (TypeState 0 M.empty (functions, M.empty))
    return ((\(xs', st, _) -> (st, map thd xs')) <$> x)

  thd :: (a, b, c) -> c
  thd (_, _, x) = x