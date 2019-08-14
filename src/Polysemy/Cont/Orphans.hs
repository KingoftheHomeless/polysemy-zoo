{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Polysemy.Cont.Orphans where

import Polysemy
import qualified Polysemy.Cont as P
import Control.Monad.Cont (MonadCont(..))

-----------------------------------------------------------------------------
-- | Orphan instance of 'MonadCont' for 'Sem'.
instance Member (P.Cont ref) r => MonadCont (Sem r) where
  callCC = P.callCC
  {-# INLINE callCC #-}
