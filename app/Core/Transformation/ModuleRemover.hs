{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
module Core.Transformation.ModuleRemover where
  import Core.Parser.AST.Expression
  import Core.Parser.AST.Literal
  import Core.Checker.Definition.Type
  import Core.Checker.Unification hiding (TypeState(..))
  import Core.Checker.Checker
  import Control.Monad.State
  import qualified Data.Map as M
  import Core.Transformation.Monomorphization hiding (getName)
  import Control.Monad.Extra
  import Data.Either
  import Core.Checker.Substitution
  import Debug.Trace

  type Environment = M.Map (Annoted String Type) String
  data ModuleState = ModuleState {
    env :: Environment,
    types :: Environment,
    counter :: Int
  } deriving Show
  type MonadModule m = (MonadState ModuleState m, MonadIO m)

  appendPrefix :: MonadModule m => String -> [Located (Toplevel Type)] -> m [Located (Toplevel Type)]
  appendPrefix prefix tl = do
    m <- (,) <$> gets env <*> gets types
    let ((e', t'), xs) = foldl (\((acc, tys), xs') -> \case
          TFunction a ret name args body :>: pos -> do
            let funTy = map (\(_ :@ ty) -> ty) args :-> ret
            ((M.insert (name :@ funTy) (prefix ++ name) acc, tys), xs' ++ [TFunction a ret (prefix ++ name) args body :>: pos])
          TAssignment (name :@ t) expr :>: pos -> ((M.insert (name :@ t) (prefix ++ name) acc, tys), xs' ++ [TAssignment ((prefix ++ name) :@ t) expr :>: pos])
          TConstant (name :@ t) expr :>: pos -> ((M.insert (name :@ t) (prefix ++ name) acc, tys), xs' ++ [TConstant ((prefix ++ name) :@ t) expr :>: pos])
          TStructure annots name fields :>: pos -> do
            let name' = if name == "Closure" then name else prefix ++ name
            ((acc, M.insert (name :@ if null annots then TId name else buildFun annots (TId name)) name' tys), xs' ++ [TStructure annots name' fields :>: pos])
          x -> ((acc, tys), xs' ++ [x])) (m, []) tl
    modify $ \s -> s { env = e', types = t' }
    return xs

  getName :: Type -> String
  getName (TId x) = x
  getName (TApp x _) = getName x
  getName _ = ""

  getAnnots :: Type -> [Type]
  getAnnots (TApp n x) = getAnnots n ++ [x]
  getAnnots (TId _) = []
  getAnnots x = [x]

  removeType :: MonadModule m => Type -> m Type
  removeType t@(TApp _ _) = do
    x <- findM (\((_ :@ t'), _) -> isRight <$> mguM t t') =<< (M.toList <$> gets types)
    case x of
      Just (_ :@ t', replacement) -> do
        traceShowM (t, t')
        s <- mguM t' t
        case s of
          Right s' -> do
            let t'' = apply s' (buildFun (getAnnots t') (TId replacement))
            traceShowM t''
            return t''
          Left _ -> return t
      Nothing -> return t
  removeType (TId n) = do
    x <- findM (\((_ :@ t'), _) -> isRight <$> mguM (TId n) t') =<< (M.toList <$> gets types)
    case x of
      Just (_ :@ _, replacement) -> return (TId replacement)
      Nothing -> return (TId n)
  removeType (x :-> ret) = do
    x' <- mapM removeType x
    ret' <- removeType ret
    return $ x' :-> ret'
  removeType (TPtr x) = do
    x' <- removeType x
    return $ TPtr x'
  removeType x = return x
  
  removeModules :: MonadModule m => Located (Toplevel Type) -> m (Located (Toplevel Type))
  removeModules (TAssignment (name :@ t) expr :>: pos) = do
    expr' <- removeExpr expr
    t' <- removeType t
    return $ TAssignment (name :@ t') expr' :>: pos
  removeModules (TFunction annots ret name args body :>: pos) = do
    body' <- mapM removeStmt body
    ret' <- removeType ret
    args' <- mapM (\(x :@ y) -> do
      y' <- removeType y
      return (x :@ y')) args
    return $ TFunction annots ret' name args' body' :>: pos
  removeModules (TStructure annots name fields :>: pos) = do
    fields' <- mapM (\(x :@ y) -> do
      y' <- removeType y
      return (x :@ y')) fields
    return $ TStructure annots name fields' :>: pos
  removeModules (TConstant (name :@ t) expr :>: pos) = do
    expr' <- removeExpr expr
    return $ TConstant (name :@ t) expr' :>: pos
  removeModules (TExport expr :>: pos) = do
    expr' <- removeModules expr
    return $ TExport expr' :>: pos
  removeModules x = return x

  removeStmt :: MonadModule m => Located (Statement Type) -> m (Located (Statement Type))
  removeStmt (SAssignment (name :@ ty) expr :>: pos) = do
    expr' <- removeExpr expr
    ty' <- removeType ty
    return $ SAssignment (name :@ ty') expr' :>: pos
  removeStmt (SIf cond then' else' :>: pos) = do
    cond' <- removeExpr cond
    then'' <- removeExpr then'
    else'' <- case else' of
      Nothing -> return Nothing
      Just x -> do
        x' <- removeExpr x
        return $ Just x'
    return $ SIf cond' then'' else'' :>: pos
  removeStmt (SExpression expr :>: pos) = do
    expr' <- removeExpr expr
    return $ SExpression expr' :>: pos
  removeStmt (SReturn expr :>: pos) = do
    expr' <- removeExpr expr
    return $ SReturn expr' :>: pos
  removeStmt (SConstant (name :@ ty) expr :>: pos) = do
    expr' <- removeExpr expr
    ty' <- removeType ty
    return $ SConstant (name :@ ty') expr' :>: pos
  removeStmt (SModified name expr :>: pos) = do
    expr' <- removeExpr expr
    return $ SModified name expr' :>: pos

  removeExpr :: MonadModule m => Located (Expression Type) -> m (Located (Expression Type))
  removeExpr (ECall n xs t :>: pos) = do
    n' <- removeExpr n
    xs' <- mapM removeExpr xs
    t' <- removeType t
    return $ ECall n' xs' t' :>: pos
  removeExpr (EBinaryOp op x y :>: pos) = do
    x' <- removeExpr x
    y' <- removeExpr y
    return $ EBinaryOp op x' y' :>: pos
  removeExpr (EUnaryOp op x :>: pos) = do
    x' <- removeExpr x
    return $ EUnaryOp op x' :>: pos
  removeExpr (ETernary cond x y :>: pos) = do
    cond' <- removeExpr cond
    x' <- removeExpr x
    y' <- removeExpr y
    return $ ETernary cond' x' y' :>: pos
  removeExpr (EArrayLiteral xs :>: pos) = do
    xs' <- mapM removeExpr xs
    return $ EArrayLiteral xs' :>: pos
  removeExpr (EStructureLiteral xs :>: pos) = do
    xs' <- mapM (\(x, y) -> do
      y' <- removeExpr y
      return (x, y')) xs
    return $ EStructureLiteral xs' :>: pos
  removeExpr (EArrayAccess x y :>: pos) = do
    x' <- removeExpr x
    y' <- removeExpr y
    return $ EArrayAccess x' y' :>: pos
  removeExpr (EStructureAccess x y :>: pos) = do
    x' <- removeExpr x
    return $ EStructureAccess x' y :>: pos
  removeExpr (ECast t x :>: pos) = do
    x' <- removeExpr x
    t' <- removeType t
    return $ ECast t' x' :>: pos
  removeExpr (ELambda annots ret args body  t:>: pos) = do
    body' <- removeExpr body
    ret' <- removeType ret
    args' <- mapM (\(x :@ y) -> do
      y' <- removeType y
      return (x :@ y')) args
    return $ ELambda annots ret' args' body' t :>: pos
  removeExpr (EReference x :>: pos) = do
    x' <- removeExpr x
    return $ EReference x' :>: pos
  removeExpr (EDereference x :>: pos) = do
    x' <- removeExpr x
    return $ EDereference x' :>: pos
  removeExpr (EBlock xs :>: pos) = do
    xs' <- mapM removeStmt xs
    return $ EBlock xs' :>: pos
  removeExpr (EVariable n t c :>: pos) = do
    x <- findM (\((name :@ t'), _) -> do
      x <- isRight <$> mguM t t'
      return $ x && name == n) =<< (M.toList <$> gets env)
    t' <- removeType t
    case x of
      Just (_, replacement) -> return (EVariable replacement t' c :>: pos)
      Nothing -> return (EVariable n t' c :>: pos)
  removeExpr (ESizeOf t :>: pos) = do
    t' <- removeType t
    return $ ESizeOf t' :>: pos
  removeExpr (ELetIn (name :@ t) expr body :>: pos) = do
    t' <- removeType t
    expr' <- removeExpr expr
    body' <- removeExpr body
    return $ ELetIn (name :@ t') expr' body' :>: pos
  removeExpr x = return x

  bundleModule :: MonadModule m => Module -> m [Located (Toplevel Type)]
  bundleModule (Module _ xs) = do
    c <- gets counter 
    modify $ \s -> s { counter = c + 1 }
    xs' <- appendPrefix ("m" ++ show c ++ "_") xs
    xs'' <- mapM removeModules xs'
    return xs''

  bundleModules :: MonadModule m => [Located (Toplevel Type)] -> M.Map String Module -> m [Located (Toplevel Type)]
  bundleModules xs mods = do
    xs' <- mapM bundleModule mods
    xs'' <- mapM removeModules xs
    return $ concat xs' ++ xs''

  bundle :: MonadIO m => [Located (Toplevel Type)] -> M.Map String Module -> m [Located (Toplevel Type)]
  bundle xs mods = do
    let s = ModuleState { env = M.empty, types = M.empty, counter = 0 }
    evalStateT (bundleModules xs mods) s