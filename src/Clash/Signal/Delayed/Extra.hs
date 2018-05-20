{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Clash.Signal.Delayed.Extra (
  delay,
  delayI,
  pipelineTreeFold,
  ) where


import           Clash.Explicit.Signal.Delayed (DSignal, toSignal,
                                                unsafeFromSignal)
import           Clash.Signal                  (HiddenClock)
import qualified Clash.Signal                  as S (delay)
import           Clash.Signal.Internal         (Domain)

import           Clash.Sized.Vector            (Vec, dtfold)

import           Clash.Promoted.Nat

import           Data.Proxy
import           Data.Singletons.Prelude

import           GHC.TypeLits                  (KnownNat, Nat)

import           Clash.XException              (maybeX)

-- | Delay a 'DSignal' for one cycle, the value at time 0 is /undefined/.
--
-- >>> fmap maybeX $ sampleN 6 (toSignal (delay (dfromList [1..])))
-- [Nothing,Just 1,Just 2,Just 3,Just 4,Just 5]
delay :: (HiddenClock domain gated)
             => DSignal domain delay a
             -> DSignal domain (delay+1) a
delay = unsafeFromSignal . S.delay . toSignal

-- | Delay a 'DSignal' for an implicit number of cycles, the value at time 0 is
-- /undefined/.
--
-- @
-- delay2 :: ('HiddenClock' domain gated)
--        => 'DSignal' domain n Int -> 'DSignal' domain (n + 2) Int
-- delay2 = 'delayI'
-- @
--
-- >>> fmap maybeX $ sampleN 6 (toSignal (delay2 (dfromList [1..])))
-- [Nothing,Nothing,Just 1,Just 2,Just 3,Just 4]
delayI :: forall domain gated delay k a.
              ( HiddenClock domain gated
              , KnownNat k)
              => DSignal domain delay     a
              -> DSignal domain (delay+k) a
delayI = unsafeFromSignal . go (snatToInteger (SNat :: SNat k)) . toSignal
  where
    go 0 = id
    go n = S.delay . go (n-1)

data DelayDSignal (domain :: Domain) (d :: Nat) (a :: *) (f :: TyFun Nat *) :: *
type instance Apply (DelayDSignal domain d a) k = DSignal domain (d+k) a

-- | A tree structured fold that inserts a flip-flop after every operation.
pipelineTreeFold :: forall domain gated delay k a.
                  ( HiddenClock domain gated
                  , KnownNat delay
                  , KnownNat k
                  , KnownNat (2^k))
                 => (a -> a -> a)                      -- ^ Fold operation to apply
                 -> Vec (2^k) (DSignal domain delay a) -- ^ 2^k vector input
                 -> DSignal domain (delay + k) a       -- ^ Output delayed by k
pipelineTreeFold op = dtfold (Proxy :: Proxy (DelayDSignal domain delay a)) id go
  where
    go :: SNat l
       -> DSignal domain (delay + l) a
       -> DelayDSignal domain delay a @@ l
       -> DelayDSignal domain delay a @@ (l+1)
    go SNat x y = delay (op <$> x <*> y)
