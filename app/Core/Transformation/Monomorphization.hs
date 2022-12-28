{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
module Core.Transformation.Monomorphization where
  import Core.Checker.Definition.Type
  import Control.Monad.RWS
  import Control.Monad.Except
  import Core.Parser.AST.Expression
  import Core.Parser.AST.Literal
  import qualified Data.Map as M
  import Core.Checker.Unification
  import Core.Checker.Substitution
  import Data.List
  import Core.Checker.Checker
  import Data.Either
  import Data.Maybe

  data MonoState = MonoState {
    nameTypeMappings :: M.Map Type String,
    interfaces :: M.Map Type (Located (Toplevel Type)),
    variableMapping :: M.Map String (Type, Located (Expression Type)),
    result :: M.Map String (Maybe (Located (Toplevel Type))),
    tAssignments :: [Located (Toplevel Type)]
  }
  type MonadMono m = (MonadRWS () [Located (Toplevel Type)] MonoState m, MonadIO m)

  addInterface :: MonadMono m => Type -> Located (Toplevel Type) -> m ()
  addInterface t toplevel = do
    interfaces' <- gets interfaces
    modify $ \s -> s { interfaces = M.insert t toplevel interfaces' }

  tell' :: MonadMono m => String -> Maybe (Located (Toplevel Type)) -> m ()
  tell' name toplevel = do
    result' <- gets result
    modify $ \s -> s { result = M.insert name toplevel result' }

  addName :: MonadMono m => Type -> String -> m ()
  addName t name = do
    state' <- get
    put $ state' { nameTypeMappings = M.insert t name (nameTypeMappings state') }
  
  addVariable :: MonadMono m => String -> Type -> Located (Expression Type) -> m ()
  addVariable name t expr = do
    state' <- get
    put $ state' { variableMapping = M.insert name (t, expr) (variableMapping state') }
  
  getName :: MonadMono m => Type -> m (Maybe String)
  getName t = M.lookup t <$> gets nameTypeMappings

  getVariable :: MonadMono m => String -> m (Maybe (Type, Located (Expression Type)))
  getVariable name = M.lookup name <$> gets variableMapping

  findToplevelAssignment :: MonadMono m => String -> m (Maybe (Located (Toplevel Type)))
  findToplevelAssignment name = do
    assignments <- gets tAssignments
    return $ find (\case
      TAssignment (name' :@ _) _ :>: _ -> name == name'
      TConstant (name' :@ _) _ :>: _ -> name == name'
      TFunction _ _ name' _ _ :>: _ -> name == name'
      _ -> False) assignments
  
  findStructure :: MonadMono m => String -> m (Maybe (Located (Toplevel Type)))
  findStructure name = do
    assignments <- gets tAssignments
    return $ find (\case
      TStructure _ name' _ :>: _ -> name == name'
      _ -> False) assignments

  findTypeName :: Type -> String
  findTypeName (TId n) = n
  findTypeName (TApp t _) = findTypeName t
  findTypeName (TPtr t) = findTypeName t
  findTypeName (_ :-> ret) = findTypeName ret
  findTypeName _ = error "findTypeName: not implemented"

  makeName :: MonadMono m => Type -> m Type
  makeName t@(TApp _ _) = do
    let name = findTypeName t
    findStructure name >>= \case
      Just (TStructure annots name' fields :>: pos) -> do
        let t' = buildFun annots (TId name')
        mguM t t' >>= \case
          Right subst -> do
            let fields' = apply subst fields
            results <- gets result
            let name'' = showTy t
            case M.lookup name'' results of
              Just _ -> return $ TId name''
              Nothing -> do
                tell' name'' $ Nothing
                fields'' <- mapM (\(x :@ t'') -> (x :@) <$> makeName t'') fields'
                tell' name'' $ Just $ TStructure [] name'' fields'' :>: pos
                return (TId name'')
          Left err -> error err
      _ -> return t
  makeName (TPtr t) = TPtr <$> makeName t
  makeName (args :-> ret) = (:->) <$> mapM makeName args <*> makeName ret
  makeName t = return t

  containsTVar :: Type -> Bool
  containsTVar (TId _) = False
  containsTVar (TApp n x) = containsTVar n || containsTVar x
  containsTVar (TPtr t) = containsTVar t
  containsTVar (args :-> ret) = any containsTVar args || containsTVar ret
  containsTVar (TVar _) = True
  containsTVar _ = False

  monoStatement :: MonadMono m => Located (Statement Type) -> m (Located (Statement Type))
  monoStatement (SAssignment (name :@ ty) expr :>: pos) = do
    ty' <- if containsTVar ty then return ty else makeName ty
    expr' <- if containsTVar ty then return expr else monoExpression expr
    addVariable name ty' expr'
    return $ SAssignment (name :@ ty') expr' :>: pos
  monoStatement (SIf cond then' else' :>: pos) = do
    cond' <- monoExpression cond
    then'' <- monoExpression then'
    else'' <- case else' of
      Nothing -> return Nothing
      Just x -> do
        x' <- monoExpression x
        return $ Just x'
    return $ SIf cond' then'' else'' :>: pos
  monoStatement (SExpression expr :>: pos) = do
    expr' <- monoExpression expr
    return $ SExpression expr' :>: pos
  monoStatement (SReturn expr :>: pos) = do
    expr' <- monoExpression expr
    return $ SReturn expr' :>: pos
  monoStatement (SConstant (name :@ ty) expr :>: pos) = do
    ty' <- if containsTVar ty then return ty else makeName ty
    expr' <- if containsTVar ty then return expr else monoExpression expr
    addVariable name ty' expr'
    return $ SConstant (name :@ ty') expr' :>: pos
  monoStatement (SModified name expr :>: pos) = do
    expr' <- monoExpression expr
    return $ SModified name expr' :>: pos
    
  monoExpression :: MonadMono m => Located (Expression Type) -> m (Located (Expression Type))
  monoExpression (ECall n xs t :>: pos) = do
    n' <- monoExpression n
    xs' <- mapM monoExpression xs
    return $ ECall n' xs' t :>: pos
  monoExpression (EBinaryOp op x y :>: pos) = do
    x' <- monoExpression x
    y' <- monoExpression y
    return $ EBinaryOp op x' y' :>: pos
  monoExpression (EUnaryOp op x :>: pos) = do
    x' <- monoExpression x
    return $ EUnaryOp op x' :>: pos
  monoExpression (ETernary cond x y :>: pos) = do
    cond' <- monoExpression cond
    x' <- monoExpression x
    y' <- monoExpression y
    return $ ETernary cond' x' y' :>: pos
  monoExpression (EArrayLiteral xs :>: pos) = do
    xs' <- mapM monoExpression xs
    return $ EArrayLiteral xs' :>: pos
  monoExpression (EStructureLiteral xs :>: pos) = do
    xs' <- mapM (\(x, y) -> do
      y' <- monoExpression y
      return (x, y')) xs
    return $ EStructureLiteral xs' :>: pos
  monoExpression (EArrayAccess x y :>: pos) = do
    x' <- monoExpression x
    y' <- monoExpression y
    return $ EArrayAccess x' y' :>: pos
  monoExpression (EStructureAccess x y :>: pos) = do
    x' <- monoExpression x
    return $ EStructureAccess x' y :>: pos
  monoExpression (ECast t x :>: pos) = do
    x' <- monoExpression x
    t' <- makeName t
    return $ ECast t' x' :>: pos
  monoExpression (ELambda annots ret args body :>: pos) = do
    args' <- mapM (\(name :@ ty) -> do
      ty' <- makeName ty
      return (name :@ ty')) args
    ret' <- makeName ret
    body' <- monoExpression body
    return $ ELambda annots ret' args' body' :>: pos
  monoExpression (EReference x :>: pos) = do
    x' <- monoExpression x
    return $ EReference x' :>: pos
  monoExpression (EDereference x :>: pos) = do
    x' <- monoExpression x
    return $ EDereference x' :>: pos
  monoExpression (EBlock xs :>: pos) = do
    s <- get
    (xs', _, lambdas) <- runRWST (mapM monoStatement xs) () s
    put s
    return $ EBlock (concatMap (\case
      (TAssignment n e :>: pos') -> [SAssignment n e :>: pos']
      _ -> []) lambdas ++ xs') :>: pos
  monoExpression (EVariable n t c :>: pos) = do
    findToplevelAssignment n >>= \case
      Just (TFunction _ ret name args body :>: pos') -> do
        let ty = map (snd . unannotate) args :-> ret
        mguM t ty >>= \case
          Left err -> error err
          Right s -> do
            let ty' = intercalate "_" $ map showTy $ M.elems s
            let name' = name ++ "_" ++ ty'
            results <- gets result
            case M.lookup name' results of
              Just _ -> return $ EVariable name' t c :>: pos
              Nothing -> do
                tell' name' Nothing
                ret' <- makeName $ apply s ret
                args' <- mapM (\(x :@ t') -> (x :@) <$> makeName (apply s t')) args
                body' <- mapM monoStatement (apply s body)
                tell' name' $ Just . apply s $ TFunction [] ret' name' args' body' :>: pos'
                return $ EVariable name' t c :>: pos
      _ -> return $ EVariable n t c :>: pos
  monoExpression (ESizeOf t :>: pos) = do
    t' <- makeName t
    return $ ESizeOf t' :>: pos
  monoExpression (ELetIn name expr body :>: pos) = do
    expr' <- monoExpression expr
    body' <- monoExpression body
    return $ ELetIn name expr' body' :>: pos
  monoExpression x = return x
    
  lookupMgu :: MonadIO m => Type -> M.Map Type a -> m (Maybe (Type, a))
  lookupMgu t c = do
    M.toList <$> filterWithKeyM (\k _ -> isRight <$> mguM k t) c >>= \case
      [] -> return Nothing
      xs -> return . Just $ head xs

  showTy :: Type -> String
  showTy (TVar i) = "t" ++ show i
  showTy (t :-> u) = "fun_" ++ intercalate "_" (map showTy t) ++ "_" ++ showTy u
  showTy Int = "Int"
  showTy Void = "Void"
  showTy Float = "Float"
  showTy Bool = "Bool"
  showTy Char = "Char"
  showTy (TRec _) = error "Should not encounter structures in monomorphization"
  showTy (TPtr t) = "ref_" ++ showTy t
  showTy (TId s) = s
  showTy (TApp s args) = showTy s ++ "_" ++ showTy args

  mguM :: MonadIO m => Type -> Type -> m (Either String Substitution)
  mguM t1 t2 = do
    res <- runExceptT $ runRWST (mgu M.empty t1 t2) M.empty (TypeState 0 M.empty (M.empty, M.empty))
    case res of
      Left (err, _, _) -> return $ Left err
      Right (s, _, _) -> return s

  monomorphizeMain :: MonadMono m => m (Located (Toplevel Type))
  monomorphizeMain = do
    findToplevelAssignment "main" >>= \case
      Just (TFunction annots ret name args body :>: pos) -> do
        body' <- mapM monoStatement body
        ret' <- makeName ret
        args' <- mapM (\(name' :@ ty) -> do
          ty' <- makeName ty
          return (name' :@ ty')) args
        return $ TFunction annots ret' name args' body' :>: pos 
      _ -> error "main function not found"

  getExtern :: [Located (Toplevel Type)] -> [Located (Toplevel Type)]
  getExtern = filter (\case
    (TDeclaration _ :>: _) -> True
    _ -> False)

  runMono :: MonadIO m => [Located (Toplevel Type)] -> m [Located (Toplevel Type)]
  runMono xs = do
    (xs', MonoState _ _ _ res _, _) <- runRWST monomorphizeMain () (MonoState M.empty M.empty M.empty M.empty xs)
    let lambdas' = catMaybes $ M.elems res
    let externs = getExtern xs
    return (externs ++ lambdas' ++ [xs'])