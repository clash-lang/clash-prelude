{-|
Copyright  :  (C) 2013-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE Trustworthy #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module CLaSH.Signal.Explicit
  ( -- * Explicitly clocked synchronous signal
    -- $relativeclocks
    -- * Clock domain crossing
    -- ** Clock
    Domain (..)
  , ClockKind (..)
  , Clock (Clock)
  , System
  , SystemClock
  , systemClock
  , freqCalc
    -- ** Synchronisation primitive
  , unsafeSynchronizer
    -- ** Clock gating
  , clockGate#
    -- * Reset
  , ResetKind (..)
  , Reset (..)
  , SystemReset
  , systemReset
  , unsafeFromAsyncReset#
  , unsafeToAsyncReset#
  , fromSyncReset#
  , toSyncReset#
    -- * Basic circuit functions
  , register#
  , delay#
  , regEn#
    -- * Simulation functions (not synthesisable)
  , simulate#
  , simulateB#
  )
where

import Data.Proxy            (Proxy (..))
import GHC.TypeLits          (KnownNat, natVal)

import CLaSH.Signal.Bundle   (Bundle (..))
import CLaSH.Signal.Internal (Clock (Clock), ClockKind (..), Domain (..),
                              Reset (..), ResetKind (..), Signal (..),
                              clockGate#, delay#, fromSyncReset#, register#,
                              regEn#, simulate#, toSyncReset#,
                              unsafeFromAsyncReset#, unsafeToAsyncReset#)

-- import GHC.TypeLits           (KnownNat, KnownSymbol)
--
-- import CLaSH.Promoted.Nat     (SNat (..), snatToInteger)
-- import CLaSH.Promoted.Symbol  (SSymbol (..))
-- import CLaSH.Signal.Internal  (Signal (..), Clock (..), SClock (..), register#,
--                                regEn#)

{- $setup
>>> :set -XDataKinds
>>> import CLaSH.Prelude
>>> type Clk2 = Clk "clk2" 2
>>> type Clk7 = Clk "clk7" 7
>>> let clk2 = sclock :: SClock Clk2
>>> let clk7 = sclock :: SClock Clk7
>>> let oversampling = register' clk2 99 . unsafeSynchronizer clk7 clk2 . register' clk7 50
>>> let almostId = register' clk7 70 . unsafeSynchronizer clk2 clk7 . register' clk2 99 . unsafeSynchronizer clk7 clk2 . register' clk7 50
>>> type ClkA = Clk "A" 100
>>> let clkA = sclock :: SClock ClkA
>>> let oscillate = register' clkA False (CLaSH.Signal.not1 oscillate)
>>> let count = regEn' clkA 0 oscillate (count + 1)
-}

{- $relativeclocks #relativeclocks#
CλaSH supports explicitly clocked 'CLaSH.Signal's in the form of:

@
'Signal'' (clk :: 'Clock') a
@

Where @a@ is the type of the elements, and @clk@ is the clock to which the
signal is synchronised. The type-parameter, @clk@, is of the kind 'Clock' which
has types of the following shape:

@
Clk \{\- name :: \-\} 'GHC.TypeLits.Symbol' \{\- period :: \-\} 'GHC.TypeLits.Nat'
@

Where @name@ is a type-level string ('GHC.TypeLits.Symbol') representing the the
name of the clock, and @period@ is a type-level natural number ('GHC.TypeLits.Nat')
representing the clock period. Two concrete instances of a 'Clk' could be:

> type ClkA500  = Clk "A500" 500
> type ClkB3250 = Clk "B3250" 3250

The periods of these clocks are however dimension-less, they do not refer to any
explicit time-scale (e.g. nano-seconds). The reason for the lack of an explicit
time-scale is that the CλaSH compiler would not be able guarantee that the
circuit can run at the specified frequency. The clock periods are just there to
indicate relative frequency differences between two different clocks. That is, a
signal:

@
'Signal'' ClkA500 a
@

is synchronized to a clock that runs 6.5 times faster than the clock to which
the signal:

@
'Signal'' ClkB3250 a
@

is synchronized to.

* __NB__: \"Bad things\"™  happen when you actually use a clock period of @0@,
so do __not__ do that!
* __NB__: You should be judicious using a clock with period of @1@ as you can
never create a clock that goes any faster!
-}

-- * Clock domain crossing

-- ** Clock


-- | The standard system domain with a period of 1000
type System = 'Domain "system" 1000


-- | The clock for 'System'
type SystemClock = Clock 'Original System

-- | The clock for 'System'
systemClock :: SystemClock
systemClock = Clock (pure True)

-- | The reset for 'System'
type SystemReset = Reset 'Asynchronous System

-- | The reset for 'System'
systemReset :: SystemReset
systemReset = Async (False :- pure True)

-- | Calculate relative periods given a list of frequencies.
--
-- So for example, you have one part of your design connected to an ADC running
-- at 20 MHz, one part of your design connected to a DAC running at 36 MHz, and
-- the rest of your system is running at 50 MHz. What are the relative
-- (integer) clock periods in CλaSH, such that their ratios correspond to the
-- ratios between the actual clock frequencies.
--
-- For this we use 'freqCalc':
--
-- >>> freqCalc [20,36,50]
-- [45,25,18]
--
-- So that we create the proper clocks:
--
-- @
-- type ADC20 = 'Clk' \"ADC\" 45
-- type DAC36 = 'Clk' \"DAC\" 25
-- type Sys50 = 'Clk' \"Sys\" 18
--
-- sys50 :: SClock Sys50
-- sys50 = 'sclock'
--
-- adc20 :: SClock ADC20
-- adc20 = 'sclock'
--
-- dac36 :: SClock DAC36
-- dac36 = 'sclock'
-- @
--
-- __NB__: This function is /not/ synthesisable
freqCalc :: [Integer] -> [Integer]
freqCalc xs = map (`div` g) ys
  where
    p  = product xs
    ys = map (p `div`) xs
    g  = foldr1 gcd ys

-- ** Synchronisation primitive
{-# NOINLINE unsafeSynchronizer #-}
-- | The 'unsafeSynchronizer' function is a primitive that must be used to
-- connect one clock domain to the other, and will be synthesised to a (bundle
-- of) wire(s) in the eventual circuit. This function should only be used as
-- part of a proper synchronisation component, such as the following dual
-- flip-flop synchronizer:
--
-- @
-- dualFlipFlop :: SClock clkA -> SClock clkB
--              -> Signal' clkA Bit -> Signal' clkB Bit
-- dualFlipFlop clkA clkB = 'register'' clkB low . 'register'' clkB low
--                        . 'unsafeSynchronizer' clkA clkB
-- @
--
-- The 'unsafeSynchronizer' works in such a way that, given 2 clocks:
--
-- @
-- type Clk7 = 'Clk' \"clk7\" 7
--
-- clk7 :: 'SClock' Clk7
-- clk7 = 'sclock'
-- @
--
-- and
--
-- @
-- type Clk2 = 'Clk' \"clk2\" 2
--
-- clk2 :: 'SClock' Clk2
-- clk2 = 'sclock'
-- @
--
-- Oversampling followed by compression is the identity function plus 2 initial
-- values:
--
-- @
-- 'register'' clk7 i $
-- 'unsafeSynchronizer' clk2 clk7 $
-- 'register'' clk2 j $
-- 'unsafeSynchronizer' clk7 clk2 $
-- 'register'' clk7 k s
--
-- ==
--
-- i :- j :- s
-- @
--
-- Something we can easily observe:
--
-- @
-- oversampling = 'register'' clk2 99 . 'unsafeSynchronizer' clk7 clk2
--              . 'register'' clk7 50
-- almostId     = 'register'' clk7 70 . 'unsafeSynchronizer' clk2 clk7
--              . 'register'' clk2 99 . 'unsafeSynchronizer' clk7 clk2
--              . 'register'' clk7 50
-- @
--
-- >>> sampleN 37 (oversampling (fromList [1..10]))
-- [99,50,1,1,1,2,2,2,2,3,3,3,4,4,4,4,5,5,5,6,6,6,6,7,7,7,8,8,8,8,9,9,9,10,10,10,10]
-- >>> sampleN 12 (almostId (fromList [1..10]))
-- [70,99,1,2,3,4,5,6,7,8,9,10]
unsafeSynchronizer :: forall a nm1 r1 nm2 r2 . (KnownNat r1, KnownNat r2)
                   => Signal ('Domain nm1 r1) a
                   -> Signal ('Domain nm2 r2) a
unsafeSynchronizer s = s'
  where
    r1 = fromInteger (natVal (Proxy :: Proxy r1))
    r2 = fromInteger (natVal (Proxy :: Proxy r2))
    s' | r1 < r2   = compress   r2 r1 s
       | r1 > r2   = oversample r1 r2 s
       | otherwise = same s

same :: Signal domain1 a -> Signal domain2 a
same (s :- ss) = s :- same ss

oversample :: Int -> Int -> Signal domain1 a -> Signal domain2 a
oversample high low (s :- ss) = s :- oversampleS (reverse (repSchedule high low)) ss

oversampleS :: [Int] -> Signal domain1 a -> Signal domain2 a
oversampleS sched = oversample' sched
  where
    oversample' []     s       = oversampleS sched s
    oversample' (d:ds) (s:-ss) = prefixN d s (oversample' ds ss)

    prefixN 0 _ s = s
    prefixN n x s = x :- prefixN (n-1) x s

compress :: Int -> Int -> Signal domain1 a -> Signal domain2 a
compress high low s = compressS (repSchedule high low) s

compressS :: [Int] -> Signal domain1 a -> Signal domain2 a
compressS sched = compress' sched
  where
    compress' []     s           = compressS sched s
    compress' (d:ds) ss@(s :- _) = s :- compress' ds (dropS d ss)

    dropS 0 s         = s
    dropS n (_ :- ss) = dropS (n-1) ss

repSchedule :: Int -> Int -> [Int]
repSchedule high low = take low $ repSchedule' low high 1
  where
    repSchedule' cnt th rep
      | cnt < th  = repSchedule' (cnt+low) th (rep + 1)
      | otherwise = rep : repSchedule' (cnt + low) (th + high) 1

-- * Product/Signal isomorphism

-- | Simulate a (@'Unbundled' a -> 'Unbundled' b@) function given a list of
-- samples of type @a@
--
-- >>> simulateB (unbundle . register (8,8) . bundle) [(1,1), (2,2), (3,3)] :: [(Int,Int)]
-- [(8,8),(1,1),(2,2),(3,3)...
-- ...
--
-- __NB__: This function is not synthesisable
simulateB# :: (Bundle a, Bundle b) => (Unbundled domain1 a -> Unbundled domain2 b) -> [a] -> [b]
simulateB# f = simulate# (bundle . f . unbundle)
