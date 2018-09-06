{-|
Copyright  :  (C) 2013-2016, University of Twente,
                  2017     , Google Inc.
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

This module defines the explicitly clocked counterparts of the functions
defined in "Clash.Prelude". Take a look at "Clash.Signal.Explicit" to see how
you can make multi-clock designs.
-}

{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE Unsafe #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_HADDOCK show-extensions #-}

module Clash.Explicit.Prelude
  ( -- * Creating synchronous sequential circuits
    mealy
  , mealyB
  , moore
  , mooreB
  , registerB
    -- * Synchronizer circuits for safe clock domain crossings
  , dualFlipFlopSynchronizer
  , asyncFIFOSynchronizer
    -- * ROMs
  , asyncRom
  , asyncRomPow2
  , rom
  , romPow2
    -- ** ROMs initialised with a data file
  , asyncRomFile
  , asyncRomFilePow2
  , romFile
  , romFilePow2
    -- * RAM primitives with a combinational read port
  , asyncRam
  , asyncRamPow2
    -- * BlockRAM primitives
  , blockRam
  , blockRamPow2
    -- ** BlockRAM primitives initialised with a data file
  , blockRamFile
  , blockRamFilePow2
  -- ** BlockRAM read/write conflict resolution
  , readNew
    -- * Utility functions
  , window
  , windowD
  , isRising
  , isFalling
    -- * Testbench functions
  , assert
  , stimuliGenerator
  , outputVerifier
    -- * Tracing
    -- ** Simple
  , traceSignal1
  , traceVecSignal1
    -- ** Tracing in a multi-clock environment
  , traceSignal
  , traceVecSignal
    -- ** VCD dump functions
  , dumpVCD
    -- * Exported modules
    -- ** Synchronous signals
  , module Clash.Explicit.Signal
  , module Clash.Explicit.Signal.Delayed
    -- ** DataFlow interface
  , module Clash.Prelude.DataFlow
    -- ** Datatypes
    -- *** Bit vectors
  , module Clash.Sized.BitVector
  , module Clash.Prelude.BitIndex
  , module Clash.Prelude.BitReduction
    -- *** Arbitrary-width numbers
  , module Clash.Sized.Signed
  , module Clash.Sized.Unsigned
  , module Clash.Sized.Index
    -- *** Fixed point numbers
  , module Clash.Sized.Fixed
    -- *** Fixed size vectors
  , module Clash.Sized.Vector
    -- *** Perfect depth trees
  , module Clash.Sized.RTree
    -- ** Annotations
  , module Clash.Annotations.TopEntity
    -- ** Type-level natural numbers
  , module GHC.TypeLits
  , module GHC.TypeLits.Extra
  , module Clash.Promoted.Nat
  , module Clash.Promoted.Nat.Literals
  , module Clash.Promoted.Nat.TH
    -- ** Type-level strings
  , module Clash.Promoted.Symbol
    -- ** Template Haskell
  , Lift (..)
    -- ** Type classes
    -- *** Clash
  , module Clash.Class.BitPack
  , module Clash.Class.Num
  , module Clash.Class.Resize
    -- *** Other
  , module Control.Applicative
  , module Data.Bits
  , module Data.Default.Class
    -- ** Exceptions
  , module Clash.XException
  , undefined
    -- ** Named types
  , module Clash.NamedTypes
    -- ** Haskell Prelude
    -- $hiding
  , module Prelude
  )
where

import Control.Applicative
import Data.Bits
import Data.Default.Class
import GHC.TypeLits
import GHC.TypeLits.Extra
import Language.Haskell.TH.Syntax  (Lift(..))
import Prelude hiding
  ((++), (!!), concat, drop, foldl, foldl1, foldr, foldr1, head, init, iterate,
   last, length, map, repeat, replicate, reverse, scanl, scanr, splitAt, tail,
   take, unzip, unzip3, zip, zip3, zipWith, zipWith3, undefined)

import Clash.Annotations.TopEntity
import Clash.Class.BitPack
import Clash.Class.Num
import Clash.Class.Resize
import Clash.NamedTypes
import Clash.Explicit.BlockRam
import Clash.Explicit.BlockRam.File
import Clash.Explicit.Mealy
import Clash.Explicit.Moore
import Clash.Explicit.RAM
import Clash.Explicit.ROM
import Clash.Explicit.ROM.File
import Clash.Explicit.Prelude.Safe
import Clash.Explicit.Signal
import Clash.Explicit.Signal.Delayed
import Clash.Explicit.Synchronizer
  (dualFlipFlopSynchronizer, asyncFIFOSynchronizer)
import Clash.Explicit.Testbench
import Clash.Prelude.BitIndex
import Clash.Prelude.BitReduction
import Clash.Prelude.DataFlow
import Clash.Prelude.ROM            (asyncRom, asyncRomPow2)
import Clash.Prelude.ROM.File       (asyncRomFile, asyncRomFilePow2)
import Clash.Promoted.Nat
import Clash.Promoted.Nat.TH
import Clash.Promoted.Nat.Literals
import Clash.Promoted.Symbol
import Clash.Signal.Trace
import Clash.Sized.BitVector
import Clash.Sized.Fixed
import Clash.Sized.Index
import Clash.Sized.RTree
import Clash.Sized.Signed
import Clash.Sized.Unsigned
import Clash.Sized.Vector
import Clash.XException

{- $setup
>>> :set -XDataKinds -XTypeApplications
>>> import Clash.Explicit.Prelude
>>> let window4 = window @3
>>> let windowD3 = windowD @2
-}

-- | Give a window over a 'Signal'
--
-- @
-- window4
---  :: Clock domain gated -> Reset domain synchronous
--   -> 'Signal' domain Int -> 'Vec' 4 ('Signal' domain Int)
-- window4 = 'window'
-- @
--
-- >>> simulateB (window4 systemClockGen systemResetGen) [1::Int,2,3,4,5] :: [Vec 4 Int]
-- [<1,0,0,0>,<2,1,0,0>,<3,2,1,0>,<4,3,2,1>,<5,4,3,2>...
-- ...
window
  :: (KnownNat n, Default a, Undefined a)
  => Clock domain gated
  -- ^ Clock to which the incoming signal is synchronized
  -> Reset domain synchronous
  -> Signal domain a               -- ^ Signal to create a window over
  -> Vec (n + 1) (Signal domain a) -- ^ Window of at least size 1
window clk rst x = res
  where
    res  = x :> prev
    prev = case natVal (asNatProxy prev) of
             0 -> repeat def
             _ -> let next = x +>> prev
                  in  registerB clk rst (repeat def) next
{-# INLINABLE window #-}

-- | Give a delayed window over a 'Signal'
--
-- @
-- windowD3 :: Clock domain gated -> Reset domain synchronous
--          -> 'Signal' domain Int -> 'Vec' 3 ('Signal' domain Int)
-- windowD3 = 'windowD'
-- @
--
-- >>> simulateB (windowD3 systemClockGen systemResetGen) [1::Int,2,3,4] :: [Vec 3 Int]
-- [<0,0,0>,<1,0,0>,<2,1,0>,<3,2,1>,<4,3,2>...
-- ...
windowD
  :: (KnownNat n, Default a, Undefined a)
  => Clock domain gated
  -- ^ Clock to which the incoming signal is synchronized
  -> Reset domain synchronous
  -> Signal domain a                -- ^ Signal to create a window over
  -> Vec (n + 1) (Signal domain a)  -- ^ Window of at least size 1
windowD clk rst x =
  let prev = registerB clk rst (repeat def) next
      next = x +>> prev
  in  prev
{-# INLINABLE windowD #-}
