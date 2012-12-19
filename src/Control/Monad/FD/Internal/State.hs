{-# LANGUAGE
    FlexibleInstances
  , MultiParamTypeClasses #-}
module Control.Monad.FD.Internal.State
       ( StateT
       , evalStateT
       , get
       , put
       , modify
       , gets
       ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class (MonadTrans (lift))

newtype StateT s m a = StateT { runStateT :: s -> m (Pair a s) }

data Pair a b = a :*: !b

evalStateT :: Monad m => StateT s m a -> s -> m a
evalStateT m s = do
  a :*: _ <- runStateT m s
  return a

state :: Monad m => (s -> Pair a s) -> StateT s m a
state f = StateT $ return . f

instance Functor m => Functor (StateT s m) where
  fmap f m = StateT $ \ s ->
    fmap (\ (a :*: s') -> f a :*: s') $ runStateT m s

instance (Functor m, Monad m) => Applicative (StateT s m) where
  pure = return
  (<*>) = ap

instance (Functor m, MonadPlus m) => Alternative (StateT s m) where
  empty = mzero
  (<|>) = mplus

instance Monad m => Monad (StateT s m) where
  return a = state $ \ s -> a :*: s
  m >>= k = StateT $ \ s -> do
    a :*: s' <- runStateT m s
    runStateT (k a) s'
  fail str = StateT $ \ _ -> fail str

instance MonadPlus m => MonadPlus (StateT s m) where
  mzero = StateT $ \ _ -> mzero
  m `mplus` n = StateT $ \ s -> runStateT m s `mplus` runStateT n s

instance MonadTrans (StateT s) where
  lift m = StateT $ \ s -> do
    a <- m
    return $ a :*: s

get :: Monad m => StateT s m s
get = state $ \ s -> s :*: s

put :: Monad m => s -> StateT s m ()
put s = s `seq` state $ \ _ -> () :*: s

modify :: Monad m => (s -> s) -> StateT s m ()
modify f = do
  s <- get
  put $! f s

gets :: Monad m => (s -> a) -> StateT s m a
gets f = do
  s <- get
  return $ f s
