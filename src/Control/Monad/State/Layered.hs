{-# LANGUAGE ExplicitForAll         #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE Strict #-}
{-# EXT      InlineAll              #-}

module Control.Monad.State.Layered where

import Prelude --hiding ((.))

import Control.Applicative
-- import Control.Lens.Utils
import Control.Monad.Base
-- import Control.Monad.Branch
import Control.Monad.Catch
import Control.Monad.Fail
import Control.Monad.Identity
import Control.Monad.IO.Class
import Control.Monad.Primitive
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Data.Constraint
import Data.Default
import Data.Kind (Type)
import Control.Lens
-- import Type.Bool
import qualified Control.Monad.State.Strict as S
-- import Data.Functor.Utils


type family If (cond :: Bool) (a :: k) (b :: k) :: k where
  If cond   a a = a
  If 'True  a b = a
  If 'False a b = b


type family (a :: k) == (b :: l) where
    a == a = 'True
    a == b = 'False
-------------------
-- === State === --
-------------------

-- === Definition === --

type    State  s     = StateT s Identity
newtype StateT s m a = StateT (S.StateT s m a) deriving (Applicative, Alternative, Functor, Monad, MonadFail, MonadFix, MonadIO, MonadPlus, MonadTrans, MonadThrow, MonadBase b)
makeWrapped ''StateT

type        States  ss = StatesT ss Identity
type family StatesT ss m where
    StatesT '[]       m = m
    StatesT (s ': ss) m = StateT s (StatesT ss m)


-- === State data discovery === --

type        DiscoverStateData    (l :: k) m = DiscoverStateData' k l m
type family DiscoverStateData' k (l :: k) m where
    DiscoverStateData' Type l m = l
    DiscoverStateData' k    l m = StateData l m

type TransStateData l t m = (DiscoverStateData l (t m) ~ DiscoverStateData l m)

type family StateData l m where
    StateData l (StateT s m) = If (MatchedBases l s) s (StateData l m)
    StateData l (t m)        = StateData l m

type family MatchedBases (a :: ka) (b :: kb) :: Bool where
    MatchedBases (a :: k) (b   :: k) = a == b
    MatchedBases (a :: k) (b t :: l) = MatchedBases a b
    MatchedBases (a :: k) (b   :: l) = 'False


-- (.) :: (b -> c) -> (a -> b) -> a -> c
-- (.) f g = \x -> f (g x) ; {-# INLINE (.) #-}


-- === MonadState === --

-- Definitions

type             MonadState  l m = (MonadGetter l m, MonadSetter l m)
class Monad m => MonadGetter l m where get :: m (DiscoverStateData l m)
class Monad m => MonadSetter l m where put :: DiscoverStateData l m -> m ()

-- Instancess

instance                       Monad m                                                           => MonadGetter (l :: Type) (StateT l m) where get   = view (from _Wrapped)   S.get    ; {-# INLINE get #-}
instance                       Monad m                                                           => MonadSetter (l :: Type) (StateT l m) where put a = view (from _Wrapped) $ S.put a  ; {-# INLINE put #-}
instance {-# OVERLAPPABLE #-}  MonadGetter l m                                                   => MonadGetter (l :: Type) (StateT s m) where get   = lift $ get @l   ; {-# INLINE get #-}
instance {-# OVERLAPPABLE #-}  MonadSetter l m                                                   => MonadSetter (l :: Type) (StateT s m) where put a = lift $ put @l a ; {-# INLINE put #-}
instance {-# OVERLAPPABLE #-} (Monad m, MonadGetter__ ok l (StateT s m), ok ~ MatchedBases l s)  => MonadGetter (l :: k)    (StateT s m) where get   = get__  @ok @l   ; {-# INLINE get #-}
instance {-# OVERLAPPABLE #-} (Monad m, MonadSetter__ ok l (StateT s m), ok ~ MatchedBases l s)  => MonadSetter (l :: k)    (StateT s m) where put a = put__  @ok @l a ; {-# INLINE put #-}
instance {-# OVERLAPPABLE #-} (Monad (t m), MonadTrans t, MonadGetter l m, TransStateData l t m) => MonadGetter (l :: k)    (t m)        where get   = lift $ get @l   ; {-# INLINE get #-}
instance {-# OVERLAPPABLE #-} (Monad (t m), MonadTrans t, MonadSetter l m, TransStateData l t m) => MonadSetter (l :: k)    (t m)        where put a = lift $ put @l a ; {-# INLINE put #-}

-- Helpers

class Monad m => MonadGetter__ (ok :: Bool) l m where get__ :: m (DiscoverStateData l m)
class Monad m => MonadSetter__ (ok :: Bool) l m where put__ :: DiscoverStateData l m -> m ()

instance (Monad m, DiscoverStateData l (StateT s m) ~ s)  => MonadGetter__ 'True  l (StateT s m) where get__   = get @s          ; {-# INLINE get__ #-}
instance (Monad m, DiscoverStateData l (StateT s m) ~ s)  => MonadSetter__ 'True  l (StateT s m) where put__ a = put @s a        ; {-# INLINE put__ #-}
instance (MonadGetter l m, TransStateData l (StateT s) m) => MonadGetter__ 'False l (StateT s m) where get__   = lift $ get @l   ; {-# INLINE get__ #-}
instance (MonadSetter l m, TransStateData l (StateT s) m) => MonadSetter__ 'False l (StateT s m) where put__ a = lift $ put @l a ; {-# INLINE put__ #-}

-- Replicators

type MonadStates  ss m = (MonadGetters ss m, MonadSetters ss m)
type MonadGetters ss m = Monads__ MonadGetter ss m
type MonadSetters ss m = Monads__ MonadSetter ss m
type family Monads__ p ss m :: Constraint where
    Monads__ p (s ': ss) m = (p s m, Monads__ p ss m)
    Monads__ p '[]       m = ()


-- === Accessing === --

gets :: forall l m s a. (MonadGetter l m, s ~ DiscoverStateData l m) => Lens' s a -> m a
gets l = view l <$> get @l ; {-# INLINE gets #-}



-- === Top state accessing === --

type family TopStateData m where
    TopStateData (StateT s m) = s
    TopStateData (t m)        = TopStateData m

type MonadState'  m = (MonadGetter' m, MonadSetter' m)
type MonadGetter' m = MonadGetter (TopStateData m) m
type MonadSetter' m = MonadSetter (TopStateData m) m

get' :: forall m. MonadGetter' m => m (TopStateData m)
put' :: forall m. MonadSetter' m => TopStateData m -> m ()
get' = get @(TopStateData m) ; {-# INLINE get' #-}
put' = put @(TopStateData m) ; {-# INLINE put' #-}

gets' :: forall m s a. (MonadGetter' m, s ~ TopStateData m) => Lens' s a -> m a
gets' l = view l <$> get' ; {-# INLINE gets' #-}


-- === Construction & running === --

stateT :: (s -> m (a,s)) -> StateT s m a
stateT = StateT . S.StateT ; {-# INLINE stateT #-}

runStateT  :: forall s m a.              StateT s m a -> s -> m (a, s)
evalStateT :: forall s m a. Functor m => StateT s m a -> s -> m a
execStateT :: forall s m a. Functor m => StateT s m a -> s -> m s
runStateT    = S.runStateT  . view _Wrapped  ; {-# INLINE runStateT  #-}
evalStateT m = fmap fst . runStateT m ; {-# INLINE evalStateT #-}
execStateT m = fmap snd . runStateT m ; {-# INLINE execStateT #-}

runDefStateT  :: forall s m a.             Default s  => StateT s m a -> m (a, s)
evalDefStateT :: forall s m a. (Functor m, Default s) => StateT s m a -> m a
execDefStateT :: forall s m a. (Functor m, Default s) => StateT s m a -> m s
runDefStateT  = flip runStateT  def ; {-# INLINE runDefStateT  #-}
evalDefStateT = flip evalStateT def ; {-# INLINE evalDefStateT #-}
execDefStateT = flip execStateT def ; {-# INLINE execDefStateT #-}

runState  :: forall s a. State s a -> s -> (a, s)
evalState :: forall s a. State s a -> s -> a
execState :: forall s a. State s a -> s -> s
runState  = S.runState  . view _Wrapped ; {-# INLINE runState  #-}
evalState = S.evalState . view _Wrapped ; {-# INLINE evalState #-}
execState = S.execState . view _Wrapped ; {-# INLINE execState #-}

runDefState  :: forall s a. Default s => State s a -> (a, s)
evalDefState :: forall s a. Default s => State s a -> a
execDefState :: forall s a. Default s => State s a -> s
runDefState  = flip runState  def ; {-# INLINE runDefState  #-}
evalDefState = flip evalState def ; {-# INLINE evalDefState #-}
execDefState = flip execState def ; {-# INLINE execDefState #-}


-- === Generic state modification === --

modifyM  :: forall l s m a. (MonadState l m, s ~ DiscoverStateData l m) => (s -> m (a, s)) -> m a
modifyM_ :: forall l s m a. (MonadState l m, s ~ DiscoverStateData l m) => (s -> m     s)  -> m ()
modify   :: forall l s m a. (MonadState l m, s ~ DiscoverStateData l m) => (s ->   (a, s)) -> m a
modify_  :: forall l s m a. (MonadState l m, s ~ DiscoverStateData l m) => (s ->       s)  -> m ()
modify    = modifyM  @l . fmap return       ; {-# INLINE modify   #-}
modify_   = modifyM_ @l . fmap return       ; {-# INLINE modify_  #-}
modifyM_  = modifyM  @l . (fmap.fmap) ((),) ; {-# INLINE modifyM_ #-}
modifyM f = do (a,t) <- f =<< get @l
               a <$ put @l t
{-# INLINE modifyM #-}

subState      :: forall l s m a. (MonadState l m, s ~ DiscoverStateData l m) =>               m a -> m a
with          :: forall l s m a. (MonadState l m, s ~ DiscoverStateData l m) => s          -> m a -> m a
withModified  :: forall l s m a. (MonadState l m, s ~ DiscoverStateData l m) => (s ->   s) -> m a -> m a
withModifiedM :: forall l s m a. (MonadState l m, s ~ DiscoverStateData l m) => (s -> m s) -> m a -> m a
with              = withModified  @l . const         ; {-# INLINE with          #-}
withModified      = withModifiedM @l . fmap return   ; {-# INLINE withModified  #-}
withModifiedM f m = subState @l $ modifyM_ @l f >> m ; {-# INLINE withModifiedM #-}
subState        m = do s <- get @l
                       m <* put @l s
{-#INLINE subState #-}


-- === Top level state modification === --

modifyM'  :: forall s m a. (MonadState' m, s ~ TopStateData m) => (s -> m (a, s)) -> m a
modifyM'_ :: forall s m a. (MonadState' m, s ~ TopStateData m) => (s -> m     s)  -> m ()
modify'   :: forall s m a. (MonadState' m, s ~ TopStateData m) => (s ->   (a, s)) -> m a
modify'_  :: forall s m a. (MonadState' m, s ~ TopStateData m) => (s ->       s)  -> m ()
modify'    = modifyM'  . fmap return       ; {-# INLINE modify'   #-}
modify'_   = modifyM'_ . fmap return       ; {-# INLINE modify'_  #-}
modifyM'_  = modifyM'  . (fmap.fmap) ((),) ; {-# INLINE modifyM'_ #-}
modifyM' f = do (a,t) <- f =<< get'
                a <$ put' t
{-# INLINE modifyM' #-}

subState'      :: forall s m a. (MonadState' m, s ~ TopStateData m) =>               m a -> m a
with'          :: forall s m a. (MonadState' m, s ~ TopStateData m) => s          -> m a -> m a
withModified'  :: forall s m a. (MonadState' m, s ~ TopStateData m) => (s ->   s) -> m a -> m a
withModifiedM' :: forall s m a. (MonadState' m, s ~ TopStateData m) => (s -> m s) -> m a -> m a
with'              = withModified'  . const       ; {-# INLINE with'          #-}
withModified'      = withModifiedM' . fmap return ; {-# INLINE withModified'  #-}
withModifiedM' f m = subState' $ modifyM'_ f >> m ; {-# INLINE withModifiedM' #-}
subState'        m = do s <- get'
                        m <* put' s
{-# INLINE subState' #-}


-- === Other modifications === --

mapStateT :: (m (a, s) -> n (b, s)) -> StateT s m a -> StateT s n b
mapStateT f = _Wrapped %~ S.mapStateT f ; {-# INLINE mapStateT #-}
