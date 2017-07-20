{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE Strict #-}

module Main where

import Prelude as P
import Criterion.Main
import Control.Monad.State.Layered hiding ((.))
import qualified Control.Monad.State.Strict as S
import Control.Monad.Codensity
import qualified Control.Monad.State.CPS as CPS


mtlGettingCycle :: S.MonadState Int m => Int -> m ()
mtlGettingCycle i = repeatM i S.get ; {-# INLINE mtlGettingCycle #-}

gettingCycle :: MonadState Int m => Int -> m ()
gettingCycle i = repeatM i (get @Int) ; {-# INLINE gettingCycle #-}

-- mtlgettingCycle :: MonadState Int m => Int -> m ()
-- mtlgettingCycle i = repeatM i S.get ; {-# INLINE mtlGettingCycle #-}


mtlIncState :: S.MonadState Int m => m ()
mtlIncState = S.modify succ ; {-# INLINE mtlIncState #-}

incState :: MonadState Int m => m ()
incState = modify_ @Int succ ; {-# INLINE incState #-}

incPure :: Int -> Int
incPure = succ ; {-# INLINE incPure #-}

repeatM :: Monad m => Int -> m a -> m ()
repeatM i f = let r 0 = pure (); r i = f >> r (i - 1) in r i ; {-# INLINE repeatM #-}

repeatP :: Int -> (a -> a) -> a -> a
repeatP i f a = let r 0 a = a; r i a = r (i - 1) (f a) in r i a ; {-# INLINE repeatP #-}

main = do
    putStrLn "Testing time overhead of monad transformers"
    putStrLn "IMPORTANT: These times should be THE SAME. If they are not, you've broken then implementation. Go back and fix it."
    defaultMain
        [ bgroup "monad transformers overhead"
            [ bench "0 trans (10e6)"      $ whnf (flip (evalState @Int) 0) (repeatM 1000000 incState)
            , bench "1R trans (10e6)"     $ whnf (flip (evalState @Int) 0 . flip (evalStateT @String) "") (repeatM 1000000 incState)
            , bench "1L trans (10e6)"     $ whnf (flip (evalState @String) "" . flip (evalStateT @Int) 0) (repeatM 1000000 incState)
            , bench "2R trans (10e6)"     $ whnf (flip (evalState @Int) 0 . flip (evalStateT @String) "" . flip (evalStateT @Char) 'x') (repeatM 1000000 incState)
            , bench "2L trans (10e6)"     $ whnf (flip (evalState @Char) 'x' . flip (evalStateT @String) "" . flip (evalStateT @Int) 0) (repeatM 1000000 incState)
            , bench "3R trans (10e6)"     $ whnf (flip (evalState @Int) 0 . flip (evalStateT @String) "" . flip (evalStateT @Char) 'x' . flip (evalStateT @()) ()) (repeatM 1000000 incState)
            , bench "3L trans (10e6)"     $ whnf (flip (evalState @()) () . flip (evalStateT @Char) 'x' . flip (evalStateT @String) "" . flip (evalStateT @Int) 0) (repeatM 1000000 incState)
            ]
        ]

    putStrLn ""
    defaultMain
        [ bgroup "mtl monad transformers overhead"
            [ bench "0 trans (10e6)"      $ whnf (flip S.evalState 0) (repeatM 1000000 mtlIncState)
            -- , bench "1R trans (10e6)"     $ whnf (flip (evalState @Int) 0 . flip (evalStateT @String) "") (repeatM 1000000 incState)
            -- , bench "1L trans (10e6)"     $ whnf (flip (evalState @String) "" . flip (evalStateT @Int) 0) (repeatM 1000000 incState)
            -- , bench "2R trans (10e6)"     $ whnf (flip (evalState @Int) 0 . flip (evalStateT @String) "" . flip (evalStateT @Char) 'x') (repeatM 1000000 incState)
            -- , bench "2L trans (10e6)"     $ whnf (flip (evalState @Char) 'x' . flip (evalStateT @String) "" . flip (evalStateT @Int) 0) (repeatM 1000000 incState)
            -- , bench "3R trans (10e6)"     $ whnf (flip (evalState @Int) 0 . flip (evalStateT @String) "" . flip (evalStateT @Char) 'x' . flip (evalStateT @()) ()) (repeatM 1000000 incState)
            -- , bench "3L trans (10e6)"     $ whnf (flip (evalState @()) () . flip (evalStateT @Char) 'x' . flip (evalStateT @String) "" . flip (evalStateT @Int) 0) (repeatM 1000000 incState)
            ]

        , bgroup "cps monad transformers overhead"
            [ bench "0 trans (10e6)"      $ whnf (flip CPS.evalState 0) (repeatM 1000000 mtlIncState)
            -- , bench "1R trans (10e6)"     $ whnf (flip (evalState @Int) 0 . flip (evalStateT @String) "") (repeatM 1000000 incState)
            -- , bench "1L trans (10e6)"     $ whnf (flip (evalState @String) "" . flip (evalStateT @Int) 0) (repeatM 1000000 incState)
            -- , bench "2R trans (10e6)"     $ whnf (flip (evalState @Int) 0 . flip (evalStateT @String) "" . flip (evalStateT @Char) 'x') (repeatM 1000000 incState)
            -- , bench "2L trans (10e6)"     $ whnf (flip (evalState @Char) 'x' . flip (evalStateT @String) "" . flip (evalStateT @Int) 0) (repeatM 1000000 incState)
            -- , bench "3R trans (10e6)"     $ whnf (flip (evalState @Int) 0 . flip (evalStateT @String) "" . flip (evalStateT @Char) 'x' . flip (evalStateT @()) ()) (repeatM 1000000 incState)
            -- , bench "3L trans (10e6)"     $ whnf (flip (evalState @()) () . flip (evalStateT @Char) 'x' . flip (evalStateT @String) "" . flip (evalStateT @Int) 0) (repeatM 1000000 incState)
            ]

        , bgroup "codensity monad transformers overhead"
            [ bench "0 trans (10e6)"      $ whnf (flip (evalState @Int) 0 . lowerCodensity) (repeatM 1000000 incState)
            , bench "1R trans (10e6)"     $ whnf (flip (evalState @Int) 0 . lowerCodensity . flip (evalStateT @String) "" . lowerCodensity) (repeatM 1000000 incState)
            , bench "1L trans (10e6)"     $ whnf (flip (evalState @String) "" . lowerCodensity . flip (evalStateT @Int) 0 . lowerCodensity) (repeatM 1000000 incState)
            , bench "2R trans (10e6)"     $ whnf (flip (evalState @Int) 0 . lowerCodensity . flip (evalStateT @String) "" . lowerCodensity . flip (evalStateT @Char) 'x' . lowerCodensity) (repeatM 1000000 incState)
            , bench "2L trans (10e6)"     $ whnf (flip (evalState @Char) 'x' . lowerCodensity . flip (evalStateT @String) "" . lowerCodensity . flip (evalStateT @Int) 0 . lowerCodensity) (repeatM 1000000 incState)
            , bench "3R trans (10e6)"     $ whnf (flip (evalState @Int) 0 . lowerCodensity . flip (evalStateT @String) "" . lowerCodensity . flip (evalStateT @Char) 'x' . lowerCodensity . flip (evalStateT @()) () . lowerCodensity) (repeatM 1000000 incState)
            , bench "3L trans (10e6)"     $ whnf (flip (evalState @()) () . lowerCodensity . flip (evalStateT @Char) 'x' . lowerCodensity . flip (evalStateT @String) "" . lowerCodensity . flip (evalStateT @Int) 0 . lowerCodensity) (repeatM 1000000 incState)
            ]



        ]
