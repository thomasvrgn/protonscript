{-# LANGUAGE LambdaCase #-}
module Core.Transformation.Free where
  import qualified Data.Map as M
  import Core.Checker.Definition.Type
  import Core.Parser.AST.Expression
  import Core.Parser.AST.Literal
  import Core.Checker.Checker

  class Free a where
    free :: a -> M.Map String Type

  instance Free (Annoted String Type) where
    free (name :@ t) = M.singleton name t
  
  instance Free a => Free (Located a) where
    free (x :>: _) = free x

  instance Free a => Free [a] where
    free = M.unions . map free

  instance Free (Toplevel Type) where
    free (TAssignment (n :@ t) e) = free e M.\\ M.singleton n t
    free (TFunction _ ret n args e) = free e M.\\ (M.singleton n funTy `M.union` free args)
      where funTy = map (snd . unannotate) args :-> ret
    free (TConstant (n :@ t) e) = free e M.\\ M.singleton n t
    free _ = M.empty

  instance (Free a, Free b) => Free (a, b) where
    free (a, b) = free a `M.union` free b

  instance {-# OVERLAPS #-} Free b => Free (String, b) where
    free (_, b) = free b

  instance Free a => Free (Maybe a) where
    free Nothing = M.empty
    free (Just x) = free x

  instance Free (Statement Type) where
    free (SAssignment (n :@ t) e) = free e M.\\ M.singleton n t
    free (SIf e s1 s2) = free e `M.union` free s1 `M.union` free s2
    free (SExpression e) = free e
    free (SReturn e) = free e
    free (SConstant (n :@ t) e) = free e M.\\ M.singleton n t
    free (SModified n e) = free e M.\\ free n
  
  instance Free (Expression Type) where
    free (EVariable n t _) = M.singleton n t
    free (ECall e args _) = free e `M.union` free args
    free (ELambda _ _ args body _) = free body M.\\ free args
    free (EArrayLiteral e) = free e
    free (EArrayAccess e1 e2) = free e1 `M.union` free e2
    free (EStructureLiteral f) = free f
    free (EStructureAccess e _) = free e
    free (ECast _ e) = free e
    free (ETernary c t e) = free c `M.union` free t `M.union` free e
    free (EUnaryOp _ e) = free e
    free (EBinaryOp _ e1 e2) = free e1 `M.union` free e2
    free (EReference e) = free e
    free (EDereference e) = free e
    free (EBlock es) = fst $ foldl (\(acc, excluded) -> \case
      SAssignment (n :@ t) e :>: _ -> (acc `M.union` free e M.\\ M.singleton n t, excluded `M.union` M.singleton n t)
      x -> (acc `M.union` free x M.\\ excluded, excluded)
      ) (M.empty, M.empty) es
    free (ELetIn n e1 e2) = (free e1 `M.union` free e2) M.\\ free n
    free _ = M.empty