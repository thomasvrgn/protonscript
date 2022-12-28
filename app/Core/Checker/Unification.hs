{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
module Core.Checker.Unification where
  import Control.Monad.RWS
  import Control.Monad.Except
  import Core.Checker.Substitution (Substitution, Types (free, apply))
  import Core.Checker.Definition.Type (Type(..), Env, ConsEnv, Scheme (Forall))
  import qualified Data.Map as M
  import Core.Checker.Definition.Methods (compose)
  import Data.List (delete, union)
  import Core.Parser.AST.Expression
  import Core.Parser.AST.Literal
  import Data.These (These(These, This, That))
  import Data.Semialign.Indexed (SemialignWithIndex(ialignWith))
  import Data.Foldable.Extra (foldlM)
  import Data.Either (isRight)

  type ReaderEnv = M.Map String Type
  data Module = Module String [Located (Toplevel Type)]
    deriving Show
  data TypeState = TypeState {
    counter :: Int,
    modules :: M.Map String Module,
    env :: Env
  } deriving Show
  type MonadType m = (MonadRWS ReaderEnv () TypeState m, MonadError (String, Maybe String, Position) m, MonadIO m)
  
  variable :: Int -> Type -> Either String Substitution
  variable n t
    | t == TVar n = Right M.empty
    | show n `elem` free t = Left $ "Occurs check failed in " ++ show t ++ " with " ++ show (TVar n)
    | otherwise = Right $ M.singleton n t

  -- Creating a array of correspondances between two arrays
  align :: (Eq b, Eq a, Eq c) => [(a, b)] -> [(a, c)] -> [((a, b), (a, c))]
  align ((x, y):xs) ys = case lookup x ys of
    Nothing -> align xs ys
    Just t -> ((x, y), (x, t)) : align xs (delete (x, t) ys)
  align [] _ = []

  ialignWithM :: (Monad m, Traversable f, SemialignWithIndex Int f) => (Int -> These a b -> m c) -> f a -> f b -> m (f c)
  ialignWithM f xs ys = sequenceA $ ialignWith f xs ys

  filterWithKeyM :: (Monad m, Ord k) => (k -> a -> m Bool) -> M.Map k a -> m (M.Map k a)
  filterWithKeyM f m = M.fromList <$> filterM (uncurry f) (M.toList m)

  check :: MonadType m => ConsEnv -> Substitution  -> Substitution  -> m (Either String Substitution) 
  check e s1 s2 = do
    m <- sequence <$> ialignWithM (\i -> \case
      This a -> return $ Right (M.singleton i (apply s1 a))
      That b -> return $ Right (M.singleton i (apply s2 b))
      These a b -> mgu e (apply s1 a) (apply s2 b)) s1 s2
    return $ foldl compose M.empty <$> m

  fresh :: MonadType m => m Type
  fresh = gets counter >>= \n -> modify (\c -> c { counter = n + 1 }) >> return (TVar n)

  lookupCons :: MonadType m => Type -> m (Maybe (Type, Scheme))
  lookupCons t = do
    (_, c) <- gets env
    M.toList <$> filterWithKeyM (\k _ -> isRight <$> mgu c k t) c >>= \case
      [] -> return Nothing
      xs -> return $ Just $ head xs

  tyInstantiate :: MonadType m => Scheme -> m Type
  tyInstantiate (Forall _ _ vars t) = do
    vars' <- mapM (const fresh) vars
    let s = M.fromList $ zip vars vars'
      in return $ apply s t  
  
  mgu :: MonadType m => ConsEnv -> Type -> Type -> m (Either String Substitution)
  mgu _ (TVar i) t = return $ variable i t
  mgu _ t (TVar i) = return $ variable i t
  mgu e a@(t1 :-> t2) b@(t3 :-> t4)
    = if length t1 /= length t3
        then 
          return $ Left $ show a ++ " has " ++ show (length t1) ++ " arguments whereas " ++ show b ++ " has " ++ show (length t3) ++ " arguments"
        else do
          s1 <- foldlM (\acc (t, t') -> do
            s' <- mgu e t t'
            case s' of
              Right s -> do
                s'' <- case acc of
                  Right s3 -> check e s s3
                  Left _ -> return acc
                return $ compose <$> s'' <*> acc
              Left s -> return $ Left s) (Right M.empty) $ zip t1 t3
          s2 <- mgu e t2 t4
          return $ compose <$> s1 <*> s2
  mgu _ Int Int = return $ Right M.empty
  mgu _ Bool Bool = return $ Right M.empty
  mgu _ Char Char = return $ Right M.empty
  mgu _ (TPtr _) (TPtr Void) = return $ Right M.empty
  mgu e (TPtr t) (TPtr t') = mgu e t t'
  mgu _ Void Void = return $ Right M.empty
  mgu e (TRec fs1) (TRec fs2) =
    let f = align fs1 fs2 `union` align fs2 fs1
      in foldM (\s (x, y) -> do
        s' <- mgu e (snd x) (snd y)
        return $ compose <$> s <*> s') (Right M.empty) f
  mgu e t (TRec fs) = lookupCons t >>= \case
    Nothing -> return $ Left $ "Type " ++ show t ++ " is not a record"
    Just (_, scheme) -> do
      tyInstantiate scheme >>= \case
        [t'] :-> id' -> do
          s <- mgu e t id'
          case s of
            Right s' -> do
              s'' <- mgu e (apply s' t') (TRec fs)
              return $ compose <$> s'' <*> s
            Left s' -> return $ Left s'
        _ -> return $ Left $ "Type " ++ show t ++ " is not a record"
  mgu e (TRec fs) t = lookupCons t >>= \case
    Nothing -> return $ Left $ "Type " ++ show t ++ " is not a record"
    Just (_, scheme) -> do
      tyInstantiate scheme >>= \case
        [t'] :-> id' -> do
          s <- mgu e t id'
          case s of
            Right s' -> do
              s'' <- mgu e (apply s' t') (TRec fs)
              return $ compose <$> s'' <*> s
            Left s' -> return $ Left s'
        _ -> return $ Left $ "Type " ++ show t ++ " is not a record"
  mgu e (TApp n xs) (TApp n' xs') = do
    s1 <- mgu e n n'
    s2 <- mgu e xs xs'
    return $ compose <$> s1 <*> s2
  mgu _ (TId n) (TId n') = if n == n' then return $ Right M.empty else return $ Left $ "Type mismatch: " ++ show n ++ " and " ++ show n'
  mgu _ s1 s2 = return $ Left $ "Type " ++ show s1 ++ " mismatches with type " ++ show s2