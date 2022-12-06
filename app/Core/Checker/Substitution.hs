module Core.Checker.Substitution where
  import Data.Map (Map)
  import Core.Checker.Definition.Type (Type)
  import qualified Data.Set as S
  
  type Substitution = Map Int Type

  class Types a where
    free  :: a -> S.Set String
    apply :: Substitution -> a -> a