{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- |utility type and function providing monad interface for fresh variable ideas
module Utils.FreshMonad where

import Control.Monad.State (MonadState,State,get,put)
import Control.Monad.Trans.Maybe (MaybeT)

import Utils.Type (Var(..))

class MonadState Int m => MonadFresh m where
  fresh :: m Int
  fresh = do
     i <- get
     put (i+1)
     pure i

-- |state monad with 'Int' state
type FreshM = State Int

instance MonadFresh FreshM
instance MonadFresh (MaybeT FreshM)

{-
-- |Returns a fresh integer by incrementing the state by 1.
fresh :: MonadFresh m => m Int
fresh = do
-}

-- |Wraps result of 'fresh' into the 'Var' datatype.
freshVar :: MonadFresh m => m Var
freshVar = Fresh <$> fresh
