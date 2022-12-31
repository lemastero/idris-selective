module Control.Selective.Verified

import Control.Selective
import Data.Either
import Control.Monad.Either

%default total

export
interface (Selective f) => VerifiedSelective (f : Type -> Type) where
  selectiveIdentity : {a : Type} -> {x : f a} ->
                      select x (pure Basics.id) = either Basics.id Basics.id <$> x
