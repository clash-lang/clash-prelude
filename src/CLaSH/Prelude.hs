{-|
  Copyright   :  (C) 2013-2016, University of Twente,
                     2017     , Google Inc.
  License     :  BSD2 (see the file LICENSE)
  Maintainer  :  Christiaan Baaij <christiaan.baaij@gmail.com>

  CλaSH (pronounced ‘clash’) is a functional hardware description language that
  borrows both its syntax and semantics from the functional programming language
  Haskell. The merits of using a functional language to describe hardware comes
  from the fact that combinational circuits can be directly modeled as
  mathematical functions and that functional languages lend themselves very well
  at describing and (de-)composing mathematical functions.

  This package provides:

  * Prelude library containing datatypes and functions for circuit design

  To use the library:

  * Import "CLaSH.Prelude"; by default clock and reset lines are implicitly
    routed for all the components found in "CLaSH.Prelude". You can read more
    about implicit clock and reset lines in "CLaSH.Signal#implicitclockandreset"
  * Alternatively, if you want to explicitly route clock and reset ports,
    for more straightforward multi-clock designs, you can import the
    "CLaSH.Explicit.Prelude" module. Note that you should not import
    "CLaSH.Prelude" and "CLaSH.Explicit.Prelude" at the same time as they
    have overlapping definitions.

  For now, "CLaSH.Prelude" is also the best starting point for exploring the
  library. A preliminary version of a tutorial can be found in "CLaSH.Tutorial".
  Some circuit examples can be found in "CLaSH.Examples".
-}

{-# LANGUAGE CPP              #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators    #-}

{-# LANGUAGE Unsafe #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module CLaSH.Prelude
  ( -- * Creating synchronous sequential circuits
    mealy
  , mealyB
  , (<^>)
  , moore
  , mooreB
  , registerB
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
    -- * Exported modules
    -- ** Synchronous signals
  , module CLaSH.Signal
  , module CLaSH.Signal.Delayed
    -- ** DataFlow interface
  , module CLaSH.Prelude.DataFlow
    -- ** Datatypes
    -- *** Bit vectors
  , module CLaSH.Sized.BitVector
  , module CLaSH.Prelude.BitIndex
  , module CLaSH.Prelude.BitReduction
    -- *** Arbitrary-width numbers
  , module CLaSH.Sized.Signed
  , module CLaSH.Sized.Unsigned
  , module CLaSH.Sized.Index
    -- *** Fixed point numbers
  , module CLaSH.Sized.Fixed
    -- *** Fixed size vectors
  , module CLaSH.Sized.Vector
    -- *** Perfect depth trees
  , module CLaSH.Sized.RTree
    -- ** Annotations
  , module CLaSH.Annotations.TopEntity
    -- ** Type-level natural numbers
  , module GHC.TypeLits
  , module GHC.TypeLits.Extra
  , module CLaSH.Promoted.Nat
  , module CLaSH.Promoted.Nat.Literals
  , module CLaSH.Promoted.Nat.TH
    -- ** Template Haskell
  , Lift (..)
    -- ** Type classes
    -- *** CLaSH
  , module CLaSH.Class.BitPack
  , module CLaSH.Class.Num
  , module CLaSH.Class.Resize
    -- *** Other
  , module Control.Applicative
  , module Data.Bits
  , module Data.Default
    -- ** Exceptions
  , module CLaSH.XException
  , undefined
    -- ** Named types
  , module CLaSH.NamedTypes
    -- ** Haskell Prelude
    -- $hiding
  , module Prelude
  )
where

import           Control.Applicative
import           Data.Bits
import           Data.Default
import           GHC.TypeLits
import           GHC.TypeLits.Extra
import           Language.Haskell.TH.Syntax  (Lift(..))
import           Prelude hiding
  ((++), (!!), concat, drop, foldl, foldl1, foldr, foldr1, head, init, iterate,
   last, length, map, repeat, replicate, reverse, scanl, scanr, splitAt, tail,
   take, unzip, unzip3, zip, zip3, zipWith, zipWith3, undefined)

import           CLaSH.Annotations.TopEntity
import           CLaSH.Class.BitPack
import           CLaSH.Class.Num
import           CLaSH.Class.Resize
import qualified CLaSH.Explicit.Prelude      as E
import           CLaSH.NamedTypes
import           CLaSH.Prelude.BitIndex
import           CLaSH.Prelude.BitReduction
import           CLaSH.Prelude.BlockRam.File
import           CLaSH.Prelude.DataFlow
import           CLaSH.Prelude.ROM.File
import           CLaSH.Prelude.Safe
import           CLaSH.Prelude.Testbench
import           CLaSH.Promoted.Nat
import           CLaSH.Promoted.Nat.TH
import           CLaSH.Promoted.Nat.Literals
import           CLaSH.Sized.BitVector
import           CLaSH.Sized.Fixed
import           CLaSH.Sized.Index
import           CLaSH.Sized.RTree
import           CLaSH.Sized.Signed
import           CLaSH.Sized.Unsigned
import           CLaSH.Sized.Vector
import           CLaSH.Signal
import           CLaSH.Signal.Delayed
import           CLaSH.XException

{- $setup
>>> :set -XDataKinds
>>> let window4  = window  :: HasClockReset domain gated synchronous => Signal domain Int -> Vec 4 (Signal domain Int)
>>> let windowD3 = windowD :: HasClockReset domain gated synchronous => Signal domain Int -> Vec 3 (Signal domain Int)
-}

{- $hiding
"CLaSH.Prelude" re-exports most of the Haskell "Prelude" with the exception of
the following: (++), (!!), concat, drop, foldl, foldl1, foldr, foldr1, head,
init, iterate, last, length, map, repeat, replicate, reverse, scanl, scanr,
splitAt, tail, take, unzip, unzip3, zip, zip3, zipWith, zipWith3.

It instead exports the identically named functions defined in terms of
'CLaSH.Sized.Vector.Vec' at "CLaSH.Sized.Vector".
-}


-- | Give a window over a 'Signal'
--
-- > window4 :: HasClockReset domain gated synchronous
-- >         => Signal domain Int -> Vec 4 (Signal domain Int)
-- > window4 = window
--
-- >>> simulateB window4 [1::Int,2,3,4,5] :: [Vec 4 Int]
-- [<1,0,0,0>,<2,1,0,0>,<3,2,1,0>,<4,3,2,1>,<5,4,3,2>...
-- ...
window
  :: (KnownNat n, Default a, HasClockReset domain gated synchronous)
  => Signal domain a          -- ^ Signal to create a window over
  -> Vec n (Signal domain a)  -- ^ Window size
window = E.window hasClock hasReset
{-# INLINE window #-}

-- | Give a delayed window over a 'Signal'
--
-- > windowD3 :: HasClockReset domain gated synchronous
-- >          => Signal domain Int -> Vec 3 (Signal domain Int)
-- > windowD3 = windowD
--
-- >>> simulateB windowD3 [1::Int,2,3,4] :: [Vec 3 Int]
-- [<0,0,0>,<1,0,0>,<2,1,0>,<3,2,1>,<4,3,2>...
-- ...
windowD
  :: (KnownNat n, Default a, HasClockReset domain gated synchronous)
  => Signal domain a         -- ^ Signal to create a window over
  -> Vec n (Signal domain a) -- ^ Window size
windowD = E.windowD hasClock hasReset
{-# INLINE windowD #-}
