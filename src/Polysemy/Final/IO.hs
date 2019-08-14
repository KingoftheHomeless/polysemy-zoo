{-# LANGUAGE TupleSections #-}
module Polysemy.Final.IO
  (
    interpretFinalGlobal
  ) where

import Control.Monad
import Control.Monad.Trans.Maybe

import Control.Exception
import Data.Functor.Compose

import Data.Maybe

import GHC.Conc

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

import Polysemy
import Polysemy.Internal
import Polysemy.Internal.Union
import Polysemy.Final
import Polysemy.Final.Internal

type TMVar a = TVar (Maybe a)

type KickTable f = HashMap ThreadId (TMVar (f ()))

takeTMVar :: TMVar a -> STM a
takeTMVar tm =
  readTVar tm >>= \case
    Just a -> writeTVar tm Nothing >> return a
    _      -> retry

readTMVar :: TMVar a -> STM a
readTMVar tm =
  readTVar tm >>= \case
    Just a -> return a
    _      -> retry

interpretFinalGlobal :: Member (Final IO) r
                     => ( forall x n
                        . IO ()
                       -> e n x
                       -> Strategic IO n x
                        )
                     -> Sem (e ': r) a
                     -> Sem r a
interpretFinalGlobal n sem = withWeaving $ \s wv ins -> do
  st  <- newTVarIO (Just s)
  res <- runMaybeT $ runViaFinalGlobal st (pure ()) wv ins n sem
  s'  <- atomically $ readTMVar st
  return (fromMaybe bomb res <$ s')


runFinalGlobal :: (Member (Final IO) r, Functor f)
               => TMVar (f ())
               -> IO ()
               -> (forall x. f (Sem r x) -> IO (f x))
               -> (forall x. f x -> Maybe x)
               -> ( forall x n
                  . IO ()
                -> e n x
                 -> Strategic IO n x
                  )
               -> Sem (e ': r) a
               -> MaybeT (Sem r) a
runFinalGlobal st restore wv ins f = usingSem $ \u -> case decomp u of
  Right (Weaving e s' wv' ex ins') ->
    fmap ex $ MaybeT $ embedFinal $ fmap getCompose $ runStrategy
          (Compose (Just s'))
          (  maybe
              (pure (Compose Nothing))
              (  fmap Compose
               . runMaybeT
               . runViaFinalGlobal st restore wv ins f
               . wv'
              )
           . getCompose
          )
          (getCompose >=> ins')
          (f restore e)
  Left g -> MaybeT $ liftSem $
    weave
      (Just ())
      (maybe (pure Nothing) (runMaybeT . runFinalGlobal st restore wv ins f))
      id
      g

runViaFinalGlobal :: (Member (Final IO) r, Functor f)
                  => TMVar (f ())
                  -> TVar (KickTable f)
                  -> (forall x. f (Sem r x) -> IO (f x))
                  -> (forall x. f x -> Maybe x)
                  -> ( forall x n f
                     . Functor f
                    => (ThreadId -> IO a -> IO (f a)) -- Kick
                    -> e n x
                    -> Sem (WithStrategy m f n) (m (f x))
                     )
                  -> Sem (e ': r) a
                  -> MaybeT IO a
runViaFinalGlobal st tble restore wv ins f = usingSem $ \u -> case decomp u of
  Right (Weaving e s' wv' ex ins') ->
    fmap ex $ MaybeT $ fmap getCompose $ runStrategy
          (Compose (Just s'))
          (  maybe
              (pure (Compose Nothing))
              (  fmap Compose
               . runMaybeT
               . runViaFinalGlobal st restore wv ins f
               . wv'
              )
           . getCompose
          )
          (getCompose >=> ins')
          (f restore e)
  Left g -> case prj g of
      Just (Weaving (WithWeaving wav) s' wv' ex' ins') ->
        MaybeT $ fmap (fmap ex' . getCompose) $
          wav
            (Compose (Just s'))
            (  maybe
                (pure (Compose Nothing))
                ( fmap Compose
                . runMaybeT
                . runViaFinalGlobal st restore wv ins f
                . wv'
                )
             . getCompose
            )
            (getCompose >=> ins')
      _ -> MaybeT $ do
        tid       <- myThreadId
        switch    <- newTVarIO False
        (s, st')  <- atomically $
          (, st) <$> takeTMVar st `orElse` do
            hm <- takeTVar tble
            case HM.lookup tid hm of
              Just st' -> (, st') <$> takeTMVar st'
              _        -> retry
        let
            kick tid' main = do
              status <- threadStatus tid'
              done   <- readTVarIO switch
              if  (status == ThreadFinished
                || status == ThreadDied
                || done) then
                main
              else do
                atomically $ do
                  hm <- takeTVar tble
                  

                main

        res <- wv (liftSem
              (
              weave
                (Just ())
                (maybe
                  (pure Nothing)
                  (  runMaybeT
                   . runFinalGlobal st restore' wv ins f)
                )
                id
                g
              ) <$ s) `onException` restore'
        atomically $ do
          writeTVar st $ Just (() <$ res)
          writeTVar switch False
          return $ join (ins res)

bomb :: a
bomb = error
  "interpretFinalGlobal: Uninspectable functorial state \
                        \still carried a result. You're likely using an interpreter \
                        \that uses 'Polysemy.Internal.Union.weave' improperly. \
                        \See documentation for more information."
