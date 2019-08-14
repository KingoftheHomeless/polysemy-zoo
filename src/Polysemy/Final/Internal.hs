{-# LANGUAGE TemplateHaskell #-}
module Polysemy.Final.Internal where

import Polysemy

-----------------------------------------------------------------------------
-- | An effect for embedding higher-order effects in the final target monad
-- of the effect stack.
--
-- This is very useful for writing interpreters that interpret higher-order
-- effects in terms of the final monad - however, these interpreters
-- are subject to very different semantics than regular ones.
--
-- For more information, see 'interpretFinal'.
newtype Final m z a where
  WithWeaving :: (  forall f
                  . Functor f
                 => f ()
                 -> (forall x. f (z x) -> m (f x))
                 -> (forall x. f x -> Maybe x)
                 -> m (f a)
                 )
              -> Final m z a

makeSem_ ''Final

-----------------------------------------------------------------------------
-- | Allows for embedding higher-order actions of the final monad
-- by providing the means of explicitly threading effects through @'Sem' r@
-- to the final monad.
--
-- Consider using 'withStrategic' instead,
-- as it provides a more user-friendly interface with nearly the same power.
--
-- You are discouraged from using 'withWeaving' directly in application code,
-- as it ties your application code directly to the final monad.
withWeaving :: forall m a r
             . Member (Final m) r
            => (  forall f
                . Functor f
               => f ()
               -> (forall x. f (Sem r x) -> m (f x))
               -> (forall x. f x -> Maybe x)
               -> m (f a)
               )
            -> Sem r a

data Strategy m f n z a where
  GetInitialState     :: Strategy m f n z (f ())
  HoistInterpretation :: (a -> n b) -> Strategy m f n z (f a -> m (f b))
  GetInspector        :: Strategy m f n z (Inspector f)

------------------------------------------------------------------------------
-- | Internal function to process Strategies in terms of 'withWeaving'.
runStrategy :: Functor f
            => f ()
            -> (forall x. f (n x) -> m (f x))
            -> (forall x. f x -> Maybe x)
            -> Sem '[Strategy m f n] a
            -> a
runStrategy s wv ins = (run .) $ interpret $ \case
  GetInitialState       -> pure s
  HoistInterpretation f -> pure $ \fa -> wv (f <$> fa)
  GetInspector          -> pure (Inspector ins)
{-# INLINE runStrategy #-}
