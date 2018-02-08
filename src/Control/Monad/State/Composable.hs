{-# LANGUAGE ExplicitForAll         #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE BangPatterns #-}
{-# EXT      InlineAll              #-}

module Control.Monad.State.Composable where

import Prelude hiding (Monoid, mappend) -- , (.)) -- https://ghc.haskell.org/trac/ghc/ticket/14001

import Control.Applicative
import Control.Lens.Utils hiding ((%=), (%%=), (<%=), (<<.=))
import Control.Lens.Internal.Context (ipeek, sell)
import Control.Monad.Base
import Control.Monad.Branch
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
import Data.Monoids
import Data.Profunctor.Strong (Strong, second')
import Type.Bool
import qualified Control.Monad.State.Strict as S

-------------------
-- === State === --
-------------------

-- === Definition === --

type    State  s     = StateT s Identity
newtype StateT s m a = StateT (S.StateT s m a) deriving (Applicative, Alternative, Functor, Monad, MonadFail, MonadFix, MonadIO, MonadPlus, MonadTrans, MonadThrow, MonadBase b, MonadBranch)
makeWrapped ''StateT

type        States  ss = StatesT ss Identity
type family StatesT ss m where
    StatesT '[]       m = m
    StatesT (s ': ss) m = StateT s (StatesT ss m)


-- === Construction & running === --

stateT :: (s -> m (a,s)) -> StateT s m a
stateT = StateT . S.StateT ; {-# INLINE stateT #-}

runStateT  :: forall s m a.              StateT s m a -> s -> m (a, s)
evalStateT :: forall s m a. Functor m => StateT s m a -> s -> m a
execStateT :: forall s m a. Functor m => StateT s m a -> s -> m s
runStateT    = S.runStateT  . unwrap  ; {-# INLINE runStateT  #-}
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
runState  = S.runState  . unwrap ; {-# INLINE runState  #-}
evalState = S.evalState . unwrap ; {-# INLINE evalState #-}
execState = S.execState . unwrap ; {-# INLINE execState #-}

runDefState  :: forall s a. Default s => State s a -> (a, s)
evalDefState :: forall s a. Default s => State s a -> a
execDefState :: forall s a. Default s => State s a -> s
runDefState  = flip runState  def ; {-# INLINE runDefState  #-}
evalDefState = flip evalState def ; {-# INLINE evalDefState #-}
execDefState = flip execState def ; {-# INLINE execDefState #-}


-- === General modifications === --

mapStateT :: (m (a, s) -> n (b, s)) -> StateT s m a -> StateT s n b
mapStateT f = _Wrapped %~ S.mapStateT f ; {-# INLINE mapStateT #-}


-- === Instances === --

instance PrimMonad m => PrimMonad (StateT s m) where
  type PrimState (StateT s m) = PrimState m
  primitive = lift . primitive ; {-# INLINE primitive #-}



-------------------------------------
-- === Non-inferred MonadState === --
-------------------------------------

-- === Definitions === --

type             MonadState  s m = (MonadGetter s m, MonadSetter s m)
class Monad m => MonadGetter s m where get :: m s
class Monad m => MonadSetter s m where put :: s -> m ()


-- === Instancess === --

instance                      Monad m         => MonadGetter s (StateT s m) where get   = wrap   S.get    ; {-# INLINE get #-}
instance                      Monad m         => MonadSetter s (StateT s m) where put a = wrap $ S.put a  ; {-# INLINE put #-}
instance {-# OVERLAPPABLE #-} MonadGetter s m => MonadGetter s (StateT t m) where get   = lift $ get      ; {-# INLINE get #-}
instance {-# OVERLAPPABLE #-} MonadSetter s m => MonadSetter s (StateT t m) where put a = lift $ put a    ; {-# INLINE put #-}


-- === Replicators === --

type MonadStates  ss m = (MonadGetters ss m, MonadSetters ss m)
type MonadGetters ss m = Monads__ MonadGetter ss m
type MonadSetters ss m = Monads__ MonadSetter ss m
type family Monads__ p ss m :: Constraint where
    Monads__ p (s ': ss) m = (p s m, Monads__ p ss m)
    Monads__ p '[]       m = ()


-- === Modifications === --

modifyM  :: forall s m a. MonadState s m => (s -> m (a, s)) -> m a
modifyM_ :: forall s m a. MonadState s m => (s -> m     s)  -> m ()
modify   :: forall s m a. MonadState s m => (s ->   (a, s)) -> m a
modify_  :: forall s m a. MonadState s m => (s ->       s)  -> m ()
modify    = modifyM  . fmap return       ; {-# INLINE modify   #-}
modify_   = modifyM_ . fmap return       ; {-# INLINE modify_  #-}
modifyM_  = modifyM  . (fmap.fmap) ((),) ; {-# INLINE modifyM_ #-}
modifyM f = do (!a,!t) <- f =<< get
               a <$ put t
{-# INLINE modifyM #-}

subState      :: forall s m a. MonadState s m =>               m a -> m a
with          :: forall s m a. MonadState s m => s          -> m a -> m a
withModified  :: forall s m a. MonadState s m => (s ->   s) -> m a -> m a
withModifiedM :: forall s m a. MonadState s m => (s -> m s) -> m a -> m a
with              = withModified  . const             ; {-# INLINE with          #-}
withModified      = withModifiedM . fmap return       ; {-# INLINE withModified  #-}
withModifiedM f m = subState @s $ modifyM_ @s f >> m  ; {-# INLINE withModifiedM #-}
subState        m = do s <- get @s
                       m <* put @s s
{-#INLINE subState #-}


-- === Lens interface === --

infix  4 %%=, <+=, <*=, <-=, <//=, <^=, <^^=, <**=, <&&=, <||=, <<>=, <%=, <<%=, <<.=, <<?=
       , <<+=, <<-=, <<*=, <<//=, <<^=, <<^^=, <<**=, <<||=, <<&&=, <<<>=
infixr 2 <<~

(%%=) :: MonadState s m => Over p ((,) r) s s a b -> p a (r, b) -> m r
l %%= f = do
  (r, s) <- l f <$> get
  put s
  return r
{-# INLINE (%%=) #-}

(<%=) :: MonadState s m => LensLike ((,)b) s s a b -> (a -> b) -> m b
l <%= f = l %%= (\b -> (b, b)) . f ; {-# INLINE (<%=) #-}

(<+=)  :: (MonadState s m, Num a)             => LensLike' ((,)a) s a -> a -> m a
(<-=)  :: (MonadState s m, Num a)             => LensLike' ((,)a) s a -> a -> m a
(<*=)  :: (MonadState s m, Num a)             => LensLike' ((,)a) s a -> a -> m a
(<//=) :: (MonadState s m, Fractional a)      => LensLike' ((,)a) s a -> a -> m a
(<^=)  :: (MonadState s m, Num a, Integral e) => LensLike' ((,)a) s a -> e -> m a
l <+=  a = l <%= (+ a)      ; {-# INLINE (<+=) #-}
l <-=  a = l <%= subtract a ; {-# INLINE (<-=) #-}
l <*=  a = l <%= (* a)      ; {-# INLINE (<*=) #-}
l <//= a = l <%= (/ a)      ; {-# INLINE (<//=) #-}
l <^=  e = l <%= (^ e)      ; {-# INLINE (<^=) #-}

(<^^=) :: (MonadState s m, Fractional a, Integral e) => LensLike' ((,)a) s a -> e -> m a
(<**=) :: (MonadState s m, Floating a) => LensLike' ((,)a) s a -> a -> m a
(<||=) :: MonadState s m => LensLike' ((,)Bool) s Bool -> Bool -> m Bool
(<&&=) :: MonadState s m => LensLike' ((,)Bool) s Bool -> Bool -> m Bool
l <^^= e = l <%= (^^ e) ; {-# INLINE (<^^=) #-}
l <**= a = l <%= (** a) ; {-# INLINE (<**=) #-}
l <||= b = l <%= (|| b) ; {-# INLINE (<||=) #-}
l <&&= b = l <%= (&& b) ; {-# INLINE (<&&=) #-}

(<<%=) :: (Strong p, MonadState s m) => Over p ((,)a) s s a b -> p a b -> m a
(<<.=) :: MonadState s m => LensLike ((,)a) s s a b -> b -> m a
l <<%= f = l %%= lmap (\a -> (a,a)) (second' f) ; {-# INLINE (<<%=) #-}
l <<.= b = l %%= \a -> (a,b) ; {-# INLINE (<<.=) #-}

(<<?=) :: MonadState s m => LensLike ((,)a) s s a (Maybe b) -> b -> m a
l <<?= b = l <<.= Just b ; {-# INLINE (<<?=) #-}

(<<+=)  :: (MonadState s m, Num a)                    => LensLike' ((,) a) s a -> a -> m a
(<<-=)  :: (MonadState s m, Num a)                    => LensLike' ((,) a) s a -> a -> m a
(<<*=)  :: (MonadState s m, Num a)                    => LensLike' ((,) a) s a -> a -> m a
(<<//=) :: (MonadState s m, Fractional a)             => LensLike' ((,) a) s a -> a -> m a
(<<^=)  :: (MonadState s m, Num a, Integral e)        => LensLike' ((,) a) s a -> e -> m a
(<<^^=) :: (MonadState s m, Fractional a, Integral e) => LensLike' ((,) a) s a -> e -> m a
(<<**=) :: (MonadState s m, Floating a)               => LensLike' ((,) a) s a -> a -> m a
(<<||=) :: MonadState s m                             => LensLike' ((,) Bool) s Bool -> Bool -> m Bool
(<<&&=) :: MonadState s m                             => LensLike' ((,) Bool) s Bool -> Bool -> m Bool
(<<<>=) :: (MonadState s m, Monoid r)                 => LensLike' ((,) r) s r -> r -> m r
l <<+=  n = l %%= \a -> (a, a + n)         ; {-# INLINE (<<+=)  #-}
l <<-=  n = l %%= \a -> (a, a - n)         ; {-# INLINE (<<-=)  #-}
l <<*=  n = l %%= \a -> (a, a * n)         ; {-# INLINE (<<*=)  #-}
l <<//= n = l %%= \a -> (a, a / n)         ; {-# INLINE (<<//=) #-}
l <<^=  n = l %%= \a -> (a, a ^ n)         ; {-# INLINE (<<^=)  #-}
l <<^^= n = l %%= \a -> (a, a ^^ n)        ; {-# INLINE (<<^^=) #-}
l <<**= n = l %%= \a -> (a, a ** n)        ; {-# INLINE (<<**=) #-}
l <<||= b = l %%= \a -> (a, a || b)        ; {-# INLINE (<<||=) #-}
l <<&&= b = l %%= \a -> (a, a && b)        ; {-# INLINE (<<&&=) #-}
l <<<>= b = l %%= \a -> (a, a `mappend` b) ; {-# INLINE (<<<>=) #-}

(<<~) :: MonadState s m => ALens s s a b -> m b -> m b
l <<~ mb = do
  b <- mb
  modify_ $ \s -> ipeek b (l sell s)
  return b
{-# INLINE (<<~) #-}

(<<>~) :: Monoid m => LensLike ((,)m) s t m m -> m -> s -> (m, t)
(<<>=) :: (MonadState s m, Monoid r) => LensLike' ((,)r) s r -> r -> m r
l <<>~ m = l <%~ (`mappend` m) ; {-# INLINE (<<>~) #-}
l <<>= r = l <%= (`mappend` r) ; {-# INLINE (<<>=) #-}

infix 4 %=
infix 4 +=, -=, *=, //=

(%=) :: forall s m a b. MonadState s m => ASetter s s a b -> (a -> b) -> m ()
l %= f = modify_ $ l %~ f

(+=), (-=), (*=) :: (MonadState s m, Num a)        => ASetter' s a -> a -> m ()
(//=)            :: (MonadState s m, Fractional a) => ASetter' s a -> a -> m ()
l +=  a = l %= (+a)
l -=  a = l %= (subtract a)
l *=  a = l %= (* a)
l //= a = l %= (/ a)

(<>=) :: (MonadState s m, Monoid a) => ASetter' s a -> a -> m ()
l <>= a = l %= (<> a)



---------------------------------
-- === Inferred MonadState === --
---------------------------------

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


-- === Definitions === --

type MonadGetter' hint m = MonadGetter (DiscoverStateData hint m) m
type MonadSetter' hint m = MonadGetter (DiscoverStateData hint m) m
type MonadState'  hint m = MonadState  (DiscoverStateData hint m) m
get' :: forall hint s m. (MonadGetter s m, s ~ DiscoverStateData hint m) => m s
put' :: forall hint s m. (MonadSetter s m, s ~ DiscoverStateData hint m) => s -> m ()
get' = get ; {-# INLINE get' #-}
put' = put ; {-# INLINE put' #-}


-- === Replicators === --

type        MonadStates'  ss m = (MonadGetters' ss m, MonadSetters' ss m)
type family MonadGetters' ss m :: Constraint where
    MonadGetters' (s ': ss) m = (MonadGetter' s m, MonadGetters' ss m)
    MonadGetters' '[]       m = ()
type family MonadSetters' ss m :: Constraint where
    MonadSetters' (s ': ss) m = (MonadSetter' s m, MonadSetters' ss m)
    MonadSetters' '[]       m = ()


-- === Modifications === --

-- modifyM  :: forall l s m a. (MonadState l m, s ~ DiscoverStateData l m) => (s -> m (a, s)) -> m a
-- modifyM_ :: forall l s m a. (MonadState l m, s ~ DiscoverStateData l m) => (s -> m     s)  -> m ()
-- modify   :: forall l s m a. (MonadState l m, s ~ DiscoverStateData l m) => (s ->   (a, s)) -> m a
-- modify_  :: forall l s m a. (MonadState l m, s ~ DiscoverStateData l m) => (s ->       s)  -> m ()
-- modify    = modifyM  @l . fmap return       ; {-# INLINE modify   #-}
-- modify_   = modifyM_ @l . fmap return       ; {-# INLINE modify_  #-}
-- modifyM_  = modifyM  @l . (fmap.fmap) ((),) ; {-# INLINE modifyM_ #-}
-- modifyM f = do (!a,!t) <- f =<< get @l
--                a <$ put @l t
-- {-# INLINE modifyM #-}
--
-- subState      :: forall l s m a. (MonadState l m, s ~ DiscoverStateData l m) =>               m a -> m a
-- with          :: forall l s m a. (MonadState l m, s ~ DiscoverStateData l m) => s          -> m a -> m a
-- withModified  :: forall l s m a. (MonadState l m, s ~ DiscoverStateData l m) => (s ->   s) -> m a -> m a
-- withModifiedM :: forall l s m a. (MonadState l m, s ~ DiscoverStateData l m) => (s -> m s) -> m a -> m a
-- with              = withModified  @l . const         ; {-# INLINE with          #-}
-- withModified      = withModifiedM @l . fmap return   ; {-# INLINE withModified  #-}
-- withModifiedM f m = subState @l $ modifyM_ @l f >> m ; {-# INLINE withModifiedM #-}
-- subState        m = do s <- get @l
--                        m <* put @l s
-- {-#INLINE subState #-}
--


-- type family TopStateData m where
--     TopStateData (StateT s m) = s
--     TopStateData (t m)        = TopStateData m
--
-- type MonadState'  m = (MonadGetter' m, MonadSetter' m)
-- type MonadGetter' m = MonadGetter (TopStateData m) m
-- type MonadSetter' m = MonadSetter (TopStateData m) m
--
-- get' :: forall m. MonadGetter' m => m (TopStateData m)
-- put' :: forall m. MonadSetter' m => TopStateData m -> m ()
-- get' = get @(TopStateData m) ; {-# INLINE get' #-}
-- put' = put @(TopStateData m) ; {-# INLINE put' #-}
--
-- gets' :: forall m s a. (MonadGetter' m, s ~ TopStateData m) => Lens' s a -> m a
-- gets' l = view l <$> get' ; {-# INLINE gets' #-}








-- === Top level state modification === --

-- modifyM'  :: forall s m a. (MonadState' m, s ~ TopStateData m) => (s -> m (a, s)) -> m a
-- modifyM'_ :: forall s m a. (MonadState' m, s ~ TopStateData m) => (s -> m     s)  -> m ()
-- modify'   :: forall s m a. (MonadState' m, s ~ TopStateData m) => (s ->   (a, s)) -> m a
-- modify'_  :: forall s m a. (MonadState' m, s ~ TopStateData m) => (s ->       s)  -> m ()
-- modify'    = modifyM'  . fmap return       ; {-# INLINE modify'   #-}
-- modify'_   = modifyM'_ . fmap return       ; {-# INLINE modify'_  #-}
-- modifyM'_  = modifyM'  . (fmap.fmap) ((),) ; {-# INLINE modifyM'_ #-}
-- modifyM' f = do (!a,!t) <- f =<< get'
--                 a <$ put' t
-- {-# INLINE modifyM' #-}
--
-- subState'      :: forall s m a. (MonadState' m, s ~ TopStateData m) =>               m a -> m a
-- with'          :: forall s m a. (MonadState' m, s ~ TopStateData m) => s          -> m a -> m a
-- withModified'  :: forall s m a. (MonadState' m, s ~ TopStateData m) => (s ->   s) -> m a -> m a
-- withModifiedM' :: forall s m a. (MonadState' m, s ~ TopStateData m) => (s -> m s) -> m a -> m a
-- with'              = withModified'  . const       ; {-# INLINE with'          #-}
-- withModified'      = withModifiedM' . fmap return ; {-# INLINE withModified'  #-}
-- withModifiedM' f m = subState' $ modifyM'_ f >> m ; {-# INLINE withModifiedM' #-}
-- subState'        m = do s <- get'
--                         m <* put' s
-- {-# INLINE subState' #-}
