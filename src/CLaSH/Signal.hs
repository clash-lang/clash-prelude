{-|
Copyright  :  (C) 2013-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MagicHash      #-}
{-# LANGUAGE Rank2Types     #-}

{-# LANGUAGE Trustworthy #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_HADDOCK show-extensions #-}

module CLaSH.Signal
  ( -- * Implicitly clocked synchronous signal
    Signal
  , Clock, ClockKind (..)
  , Reset, ResetKind (..)
  , System, SystemClock, SystemReset
    -- * Basic circuit functions
  , signal
  , register
  , delay
  , regEn
  , mux
    -- * Boolean connectives
  , (.&&.), (.||.), not1
    -- * Product/Signal isomorphism
  , Bundle(..)
    -- * Simulation functions (not synthesisable)
  , simulate
  , simulateB
    -- ** lazy versions
  , simulate_lazy
  , simulateB_lazy
    -- * List \<-\> Signal conversion (not synthesisable)
  , sample
  , sampleN
  , fromList
    -- ** lazy versions
  , sample_lazy
  , sampleN_lazy
  , fromList_lazy
    -- * QuickCheck combinators
  , testFor
    -- * Type classes
    -- ** 'Eq'-like
  , (.==.), (./=.)
    -- ** 'Ord'-like
  , compare1, (.<.), (.<=.), (.>=.), (.>.)
    -- ** 'Enum'-like
  , fromEnum1
    -- ** 'Rational'-like
  , toRational1
    -- ** 'Integral'-like
  , toInteger1
    -- ** 'Bits'-like
  , testBit1
  , popCount1
  , shift1
  , rotate1
  , setBit1
  , clearBit1
  , shiftL1
  , unsafeShiftL1
  , shiftR1
  , unsafeShiftR1
  , rotateL1
  , rotateR1
  )
where

import Control.DeepSeq       (NFData)
import GHC.Stack             (HasCallStack, withFrozenCallStack)
import Data.Bits             (Bits) -- Haddock only

import CLaSH.Signal.Internal (Clock, ClockKind (..), Reset, ResetKind (..),
                              Signal, register#, delay#, regEn#, (.==.), (./=.),
                              compare1, (.<.), (.<=.), (.>=.), (.>.), fromEnum1,
                              toRational1, toInteger1, testBit1, popCount1,
                              shift1, rotate1, setBit1, clearBit1, shiftL1,
                              unsafeShiftL1, shiftR1, unsafeShiftR1, rotateL1,
                              rotateR1, (.||.), (.&&.), not1, mux, sample,
                              sampleN, fromList, simulate#, signal, testFor,
                              sample_lazy, sampleN_lazy, simulate_lazy#,
                              fromList_lazy)
import CLaSH.Signal.Explicit (System, SystemClock, SystemReset, systemClock, systemReset)
import CLaSH.Signal.Bundle   (Bundle (..))

{- $setup
>>> let oscillate = register False (not1 oscillate)
>>> let count = regEn 0 oscillate (count + 1)
-}

-- * Basic circuit functions

{-# INLINE register #-}
-- | 'register' @i s@ delays the values in 'Signal' @s@ for one cycle, and sets
-- the value at time 0 to @i@
--
-- >>> sampleN 3 (register 8 (fromList [1,2,3,4]))
-- [8,1,2]
register :: ( ?reset :: Reset 'Asynchronous domain
            , ?clk :: Clock 'Original domain
            , HasCallStack
            )
         => a -> Signal domain a -> Signal domain a
register i d = withFrozenCallStack (register# ?reset ?clk i d)
infixr 3 `register`

delay :: (?clk :: Clock 'Original domain)
      => Signal domain a
      -> Signal domain a
delay d = withFrozenCallStack (delay# ?clk d)

{-# INLINE regEn #-}
-- | Version of 'register' that only updates its content when its second argument
-- is asserted. So given:
--
-- @
-- oscillate = 'register' False ('not1' oscillate)
-- count     = 'regEn' 0 oscillate (count + 1)
-- @
--
-- We get:
--
-- >>> sampleN 8 oscillate
-- [False,True,False,True,False,True,False,True]
-- >>> sampleN 8 count
-- [0,0,1,1,2,2,3,3]
regEn :: (?reset :: Reset 'Asynchronous domain, ?clk :: Clock 'Original domain)
      => a -> Signal domain Bool -> Signal domain a -> Signal domain a
regEn i en d = withFrozenCallStack (regEn# ?reset ?clk i en d)


simulate :: (NFData a, NFData b)
         => ((?res :: Reset 'Asynchronous System, ?clk :: Clock 'Original System)
              => Signal System a -> Signal System b)
         -> [a] -> [b]
simulate f xs = let ?clk = systemClock in
                let ?res = systemReset
                in  sample (f (fromList xs))

simulate_lazy :: ((?res :: Reset 'Asynchronous System, ?clk :: Clock 'Original System)
                   => Signal System a -> Signal System b)
              -> [a] -> [b]
simulate_lazy f xs = let ?clk = systemClock in
                     let ?res = systemReset
                     in  sample_lazy (f (fromList_lazy xs))

-- * Product/Signal isomorphism

-- | Simulate a (@'Unbundled' a -> 'Unbundled' b@) function given a list of
-- samples of type @a@
--
-- >>> simulateB (unbundle . register (8,8) . bundle) [(1,1), (2,2), (3,3)] :: [(Int,Int)]
-- [(8,8),(1,1),(2,2),(3,3)...
-- ...
--
-- __NB__: This function is not synthesisable
simulateB :: (Bundle a, Bundle b, NFData a, NFData b)
          => ((?res :: Reset 'Asynchronous System, ?clk :: Clock 'Original System)
               => Unbundled domain1 a -> Unbundled domain2 b)
          -> [a] -> [b]
simulateB f xs = let ?clk = systemClock
                     ?res = systemReset
                 in  sample (bundle (f (unbundle (fromList xs))))

-- | Simulate a (@'Unbundled' a -> 'Unbundled' b@) function given a list of
-- samples of type @a@
--
-- >>> simulateB (unbundle . register (8,8) . bundle) [(1,1), (2,2), (3,3)] :: [(Int,Int)]
-- [(8,8),(1,1),(2,2),(3,3)...
-- ...
--
-- __NB__: This function is not synthesisable
simulateB_lazy :: (Bundle a, Bundle b)
               => ((?res :: Reset 'Asynchronous System, ?clk :: Clock 'Original System)
                    => Unbundled domain1 a -> Unbundled domain2 b)
               -> [a] -> [b]
simulateB_lazy f xs = let ?clk = systemClock
                          ?res = systemReset
                      in  sample_lazy (bundle (f (unbundle (fromList_lazy xs))))
