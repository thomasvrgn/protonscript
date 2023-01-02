{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Core.Checker.Definition.Methods where
  import Core.Checker.Substitution (Types(..), Substitution)
  import Core.Checker.Definition.Type (Type(..), TypeEnv, Scheme (Forall), Env, ConsEnv)
  import qualified Data.Set as S
  import qualified Data.Map as M
  import Data.Bifunctor (second)
  import Core.Parser.AST.Expression
  import Core.Parser.AST.Literal
  
  compose :: Substitution -> Substitution -> Substitution
  compose s1 s2 = M.map (apply s1) s2 `M.union` s1

  instance Types Type where
    free (TVar i) = S.singleton $ show i 
    free (t1 :-> t2) = free t1 `S.union` free t2
    free Int = S.empty
    free (TRec fs) = S.unions $ map (free . snd) fs
    free (TPtr t) = free t
    free (TApp _ xs) = free xs
    free _ = S.empty

    apply s (TVar i) = case M.lookup i s of
      Just t -> t
      Nothing -> TVar i
    apply s (t1 :-> t2) = apply s t1 :-> apply s t2
    apply s (TRec fs) = TRec $ map (second $ apply s) fs
    apply s (TPtr t) = TPtr (apply s t)
    apply s (TApp n xs) = TApp (apply s n) $ apply s xs
    apply _ s = s
  
  instance Types a => Types [a] where
    free = foldr (S.union . free) S.empty
    apply s = map (apply s)

  instance Types TypeEnv where
    free = free . M.elems
    apply = M.map . apply
  
  instance Types ConsEnv where
    free = free . M.elems
    apply = M.map . apply

  instance Types Scheme where
    free (Forall _ _ v t) = free t S.\\ S.fromList (map show v)
    apply s (Forall m p v t) = Forall m p v (apply (foldr M.delete s v) t)
    
  instance Types a => Types (Maybe a) where
    free = maybe S.empty free
    apply s = fmap (apply s)

  unLoc :: Located a -> a
  unLoc (x :>: _) = x

  instance Types a => Types (Located a) where
    free = free . unLoc
    apply s (x :>: l) = apply s x :>: l

  instance Types a => Types (Statement a) where
    free (SAssignment (n :@ _) e) = free e S.\\ S.singleton n
    free (SIf e s1 s2) = free e `S.union` free s1 `S.union` free s2
    free (SExpression e) = free e
    free (SReturn e) = free e
    free (SConstant (n :@ _) e) = free e S.\\ S.singleton n
    free (SModified n e) = free e S.\\ free n

    apply s (SAssignment v e) = SAssignment (apply s v) (apply s e)
    apply s (SIf c t e) = SIf (apply s c) (apply s t) (apply s e)
    apply s (SExpression e) = SExpression (apply s e)
    apply s (SReturn e) = SReturn (apply s e)
    apply s (SModified n e) = SModified (apply s n) (apply s e)
    apply s (SConstant v e) = SConstant (apply s v) (apply s e)

  instance Types a => Types (Toplevel a) where
    free (TAssignment (n :@ _) e) = free e S.\\ S.singleton n
    free (TFunction _ _ n args e) = free e S.\\ (S.singleton n `S.union` free args)
    free (TConstant (n :@ _) e) = free e S.\\ S.singleton n
    free _ = S.empty

    apply s (TFunction annots ret name args body) = TFunction annots (apply s ret) name (apply s args) (apply s body)
    apply s (TAssignment n value) = TAssignment (apply s n) (apply s value)
    apply s (TStructure gen n fields) = TStructure gen n (apply s fields)
    apply s (TConstant v e) = TConstant (apply s v) (apply s e)
    apply _ x = x

  instance Types b => Types (Annoted a b) where
    free (_ :@ y) = free y
    apply s (e :@ t) = e :@ apply s t

  instance {-# OVERLAPS #-} Types b => Types (Annoted String b) where
    free (x :@ _) = S.singleton x
    apply s (x :@ t) = x :@ apply s t

  instance Types Char where
    free _ = S.empty
    apply _ = id

  instance (Types a, Types b) => Types (a, b) where
    free (a, b) = free a `S.union` free b
    apply s (a, b) = (apply s a, apply s b)

  instance Types a => Types (Expression a) where
    free (EVariable n _ _) = S.singleton n
    free (ECall e args _) = free e `S.union` free args
    free (ELambda _ _ args body _) = free body S.\\ free args
    free (EArrayLiteral e) = free e
    free (EArrayAccess e1 e2) = free e1 `S.union` free e2
    free (EStructureLiteral f) = free f
    free (EStructureAccess e _) = free e
    free (ECast _ e) = free e
    free (ETernary c t e) = free c `S.union` free t `S.union` free e
    free (EUnaryOp _ e) = free e
    free (EBinaryOp _ e1 e2) = free e1 `S.union` free e2
    free (EReference e) = free e
    free (EDereference e) = free e
    free (EBlock es) = free es
    free _ = S.empty
    
    apply s (ECall n xs t) = ECall (apply s n) (apply s xs) (apply s t)
    apply s (ELambda annots ty args b t) = ELambda annots (apply s ty) (apply s args) (apply s b) (apply s t)
    apply s (EVariable n t d) = EVariable n (apply s t) (apply s d)
    apply _ (ELiteral l) = ELiteral l
    apply s (EBinaryOp op e1 e2) = EBinaryOp op (apply s e1) (apply s e2)
    apply s (EUnaryOp op e) = EUnaryOp op (apply s e)
    apply s (EArrayLiteral xs) = EArrayLiteral (apply s xs)
    apply s (EArrayAccess e i) = EArrayAccess (apply s e) (apply s i)
    apply s (EStructureLiteral fs) = EStructureLiteral (map (second $ apply s) fs)
    apply s (EStructureAccess e p) = EStructureAccess (apply s e) p
    apply s (ETernary c t e) = ETernary (apply s c) (apply s t) (apply s e)
    apply s (EReference e) = EReference (apply s e)
    apply s (EDereference e) = EDereference (apply s e)
    apply s (EBlock ss) = EBlock (apply s ss)
    apply s (ECast e t) = ECast (apply s e) (apply s t)
    apply s (ELetIn n e1 e2) = ELetIn (apply s n) (apply s e1) (apply s e2)
    apply s (ESizeOf e) = ESizeOf (apply s e)

  applyEnv :: Types a => Substitution -> (a, b) -> (a, b)
  applyEnv s (a, b) = (apply s a, b)

  applyCons :: Types b => Substitution -> (a, b) -> (a, b)
  applyCons s (a, b) = (a, apply s b)

  applyTypes :: (TypeEnv -> TypeEnv) -> Env -> Env
  applyTypes f (ty, cons) = (f ty, cons)
  
  applyCons' :: (ConsEnv -> ConsEnv) -> Env -> Env
  applyCons' f (ty, cons) = (ty, f cons)

  union :: (Ord k1, Ord k2) => (M.Map k1 v1, M.Map k2 v2) -> (M.Map k1 v1, M.Map k2 v2) -> (M.Map k1 v1, M.Map k2 v2)
  union (m1, m2) (m3, m4) = (M.union m1 m3, M.union m2 m4)
