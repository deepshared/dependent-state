{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}

module Control.Monad.State.Dependent where

import Prologue

import qualified Control.Monad.State as State
import qualified Control.Monad.Catch (MonadMask, MonadCatch, MonadThrow)
import           Control.Monad.Fix
import           Control.Monad.Primitive


-- === Types and classes ===

newtype StateT t s m a = StateT (State.StateT s m a)
                         deriving ( Functor, Monad, Applicative, MonadIO, MonadPlus, MonadTrans, Alternative
                                  , MonadFix, MonadMask, MonadCatch, MonadThrow)

makeWrapped ''StateT

type State t s = StateT t s Identity

type MonadState t s m = (MonadGet t s m, MonadPut t s m)
class Monad m => MonadGet t s m | t m -> s where get :: t -> m s
class Monad m => MonadPut t s m | t m -> s where put :: t -> s -> m ()

fromStateT :: StateT t s m a -> State.StateT s m a
fromStateT (StateT s) = s
{-# INLINE fromStateT #-}

-- Basic instances

instance {-# OVERLAPPABLE #-} (Monad m, s ~ s') => MonadGet t s (StateT t s' m) where get _ = StateT State.get   ; {-# INLINE get #-}
instance {-# OVERLAPPABLE #-} (Monad m, s ~ s') => MonadPut t s (StateT t s' m) where put _ = StateT . State.put ; {-# INLINE put #-}

instance State.MonadState r m => State.MonadState r (StateT t s m) where
    get = StateT (lift State.get)   ; {-# INLINE get #-}
    put = StateT . lift . State.put ; {-# INLINE put #-}

instance {-# OVERLAPPABLE #-} (MonadGet tp s m, MonadTrans t, Monad (t m)) => MonadGet tp s (t m) where get = lift .  get ; {-# INLINE get #-}
instance {-# OVERLAPPABLE #-} (MonadPut tp s m, MonadTrans t, Monad (t m)) => MonadPut tp s (t m) where put = lift .: put ; {-# INLINE put #-}

-- Primitive
instance PrimMonad m => PrimMonad (StateT t s m) where
    type PrimState (StateT t s m) = PrimState m
    primitive = lift . primitive ; {-# INLINE primitive #-}


-- === Utilities ===

runT  ::            t -> StateT t s m a -> s -> m (a, s)
evalT :: Monad m => t -> StateT t s m a -> s -> m a
execT :: Monad m => t -> StateT t s m a -> s -> m s

runT  _ = State.runStateT  . fromStateT ; {-# INLINE runT  #-}
evalT _ = State.evalStateT . fromStateT ; {-# INLINE evalT #-}
execT _ = State.execStateT . fromStateT ; {-# INLINE execT #-}

run  :: t -> State t s a -> s -> (a, s)
eval :: t -> State t s a -> s -> a
exec :: t -> State t s a -> s -> s

run   = runIdentity .:. runT  ; {-# INLINE run  #-}
eval  = runIdentity .:. evalT ; {-# INLINE eval #-}
exec  = runIdentity .:. execT ; {-# INLINE exec #-}

with :: MonadState t s m => t -> (s -> s) -> m a -> m a
with t f m = do
    s <- get t
    put t $ f s
    out <- m
    put t s
    return out
{-# INLINE with #-}

modify :: MonadState t s m => t -> (s -> (s, a)) -> m a
modify t = modifyM t . fmap return
{-# INLINE modify #-}

modify_ :: MonadState t s m => t -> (s -> s) -> m ()
modify_ t = modify t . fmap (,())
{-# INLINE modify_ #-}

modifyM :: MonadState t s m => t -> (s -> m (s, a)) -> m a
modifyM t f = do
    s <- get t
    (s', a) <- f s
    put t $ s'
    return a
{-# INLINE modifyM #-}

withState :: MonadState t s m => t -> (s -> s) -> m ()
withState t f = do
    s <- get t
    put t (f s)
{-# INLINE withState #-}
