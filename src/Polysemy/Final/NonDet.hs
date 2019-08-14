module Polysemy.Final.NonDet
  (
    module Polysemy.NonDet
  , module Polysemy.Final
  , nonDetToFinal
  ) where

import Control.Applicative

import Polysemy
import Polysemy.NonDet
import Polysemy.Final

-----------------------------------------------------------------------------
-- | Run an 'NonDet' effect through a final 'Alternative'
nonDetToFinal :: (Member (Final m) r, Alternative m)
              => Sem (NonDet ': r) a
              -> Sem r a
nonDetToFinal = interpretFinal $ \case
  Empty -> pure empty
  Choose left right -> do
    left'  <- runS left
    right' <- runS right
    pure $ left' <|> right'
{-# INLINE nonDetToFinal #-}
