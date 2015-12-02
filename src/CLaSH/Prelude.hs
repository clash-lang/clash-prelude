{-# LANGUAGE CPP              #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators    #-}

{-# LANGUAGE Unsafe #-}

{-# OPTIONS_HADDOCK show-extensions #-}

{-|
  Copyright   :  (C) 2013-2015, University of Twente
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

  * Import "CLaSH.Prelude"
  * Additionally import "CLaSH.Prelude.Explicit" if you want to design
    explicitly clocked circuits in a multi-clock setting

  For now, "CLaSH.Prelude" is also the best starting point for exploring the
  library. A preliminary version of a tutorial can be found in "CLaSH.Tutorial".
  Some circuit examples can be found in "CLaSH.Examples".
-}
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
    -- ** Annotations
  , module CLaSH.Annotations.TopEntity
    -- ** Type-level natural numbers
  , module GHC.TypeLits
  , module GHC.TypeLits.Extra
  , module CLaSH.Promoted.Nat
  , module CLaSH.Promoted.Nat.Literals
  , module CLaSH.Promoted.Nat.TH
    -- ** Type-level functions
  , module CLaSH.Promoted.Ord
    -- ** Template Haskell
  , Lift (..)
#if __GLASGOW_HASKELL__ < 711
  , deriveLift
#endif
    -- ** Type classes
    -- *** CLaSH
  , module CLaSH.Class.BitPack
  , module CLaSH.Class.Num
  , module CLaSH.Class.Resize
    -- *** Other
  , module Control.Applicative
  , module Data.Bits
  , module Data.Default
    -- ** Haskell Prelude
    -- $hiding
  , module Prelude
  )
where

import Control.Applicative
import Data.Bits
import Data.Default
import GHC.TypeLits
import GHC.TypeLits.Extra
import Language.Haskell.TH.Syntax  (Lift(..))
#if __GLASGOW_HASKELL__ < 711
import Language.Haskell.TH.Lift    (deriveLift)
#endif
import Prelude                     hiding ((++), (!!), concat, drop, foldl,
                                           foldl1, foldr, foldr1, head, init,
                                           iterate, last, length, map, repeat,
                                           replicate, reverse, scanl, scanr,
                                           splitAt, tail, take, unzip, unzip3,
                                           zip, zip3, zipWith, zipWith3)

import CLaSH.Annotations.TopEntity
import CLaSH.Class.BitPack
import CLaSH.Class.Num
import CLaSH.Class.Resize
import CLaSH.Prelude.BitIndex
import CLaSH.Prelude.BitReduction
import CLaSH.Prelude.BlockRam.File (blockRamFile, blockRamFilePow2)
import CLaSH.Prelude.DataFlow
import CLaSH.Prelude.Explicit      (window, windowD)
import CLaSH.Prelude.ROM.File      (asyncRomFile,asyncRomFilePow2,romFile,
                                    romFilePow2)
import CLaSH.Prelude.Safe
import CLaSH.Prelude.Testbench     (assert, stimuliGenerator, outputVerifier)
import CLaSH.Promoted.Nat
import CLaSH.Promoted.Nat.TH
import CLaSH.Promoted.Nat.Literals
import CLaSH.Promoted.Ord
import CLaSH.Sized.BitVector
import CLaSH.Sized.Fixed
import CLaSH.Sized.Index
import CLaSH.Sized.Signed
import CLaSH.Sized.Unsigned
import CLaSH.Sized.Vector
import CLaSH.Signal
import CLaSH.Signal.Delayed
import CLaSH.Signal.Explicit       (systemClock)

{- $setup
>>> :set -XDataKinds
>>> let window4 = window :: Signal Int -> Vec 4 (Signal Int)
>>> let windowD3 = windowD :: Signal Int -> Vec 3 (Signal Int)
>>> let rP = registerB (8,8)
-}

{- $hiding
"CLaSH.Prelude" re-exports most of the Haskell "Prelude" with the exception of
the following: (++), (!!), concat, drop, foldl, foldl1, foldr, foldr1, head,
init, iterate, last, length, map, repeat, replicate, reverse, scanl, scanr,
splitAt, tail, take, unzip, unzip3, zip, zip3, zipWith, zipWith3.

It instead exports the identically named functions defined in terms of
'CLaSH.Sized.Vector.Vec' at "CLaSH.Sized.Vector".
-}
