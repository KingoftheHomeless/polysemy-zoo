module Polysemy.Final.Resource
  (
    module Polysemy.Resource
  , module Polysemy.Final
  , resourceToIOFinal
  ) where

import qualified Control.Exception as X
import Control.Monad.Trans.Maybe
import Control.Concurrent.MVar

import           Polysemy
import           Polysemy.Resource
import           Polysemy.Final


------------------------------------------------------------------------------
-- | Run a 'Resource' effect in terms of 'X.bracket' through final 'IO'
--
-- This can be used as an alternative to 'lowerResource'
--
-- /Beware/: Effects that aren't interpreted in terms of 'IO'
-- will have local state semantics in regards to 'Resource' effects
-- interpreted this way. See 'interpretFinal'.
--
-- Notably, unlike 'resourceToIO', this is not consistent with
-- 'Polysemy.State.State' unless 'Polysemy.State.runStateInIORef' is used.
-- State that seems like it should be threaded globally throughout 'bracket's
-- /will not be./
--
-- Prefer 'resourceToIO' unless it's unsafe or inefficient in the context of
-- your application.
resourceToIOFinal :: Member (Final IO) r
                  => Sem (Resource ': r) a
                  -> Sem r a
resourceToIOFinal = interpretFinal $ \case
  Bracket alloc dealloc use -> do
    a <- runS  alloc
    d <- bindS dealloc
    u <- bindS use
    pure $ X.bracket a d u

  BracketOnError alloc dealloc use -> do
    a <- runS  alloc
    d <- bindS dealloc
    u <- bindS use
    pure $ X.bracketOnError a d u
{-# INLINE resourceToIOFinal #-}


------------------------------------------------------------------------------
-- | A significantly less efficient version of 'resourceToIOFinal'', but
-- tries very hard to preserve local/global state semantics depending on the
-- order interpreters are run.
--
-- If possible, try to instead interpret effects you would like to be global in
-- 'IO', and use 'resourceToIOFinal'.
-- resourceToIOFinal' :: Member (Final IO) r
--                    => Sem (Resource ': r) a
--                    -> Sem r a
-- resourceToIOFinal' sem = withWeaving $ \s wv ins -> do
--   st <- put

  
bomb :: a
bomb = error
  "asyncToErrorThreadless: Uninspectable functorial state \
                          \still carried a result. You're likely using an interpreter \
                          \that uses 'Polysemy.Internal.Union.weave' improperly. \
                          \See documentation for more information."
