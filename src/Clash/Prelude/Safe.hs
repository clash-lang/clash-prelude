{-|
  Copyright   :  (C) 2013-2016, University of Twente,
                     2017     , Myrtle Software Ltd, Google Inc.
  License     :  BSD2 (see the file LICENSE)
  Maintainer  :  Christiaan Baaij <christiaan.baaij@gmail.com>

  __This is the <https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/safe_haskell.html Safe> API only of "Clash.Prelude"__

  CλaSH (pronounced ‘clash’) is a functional hardware description language that
  borrows both its syntax and semantics from the functional programming language
  Haskell. The merits of using a functional language to describe hardware comes
  from the fact that combinational circuits can be directly modeled as
  mathematical functions and that functional languages lend themselves very well
  at describing and (de-)composing mathematical functions.

  This package provides:

  * Prelude library containing datatypes and functions for circuit design

  To use the library:

  * Import "Clash.Prelude"
  * Additionally import "Clash.Explicit.Prelude" if you want to design
    explicitly clocked circuits in a multi-clock setting

  For now, "Clash.Prelude" is also the best starting point for exploring the
  library. A preliminary version of a tutorial can be found in "Clash.Tutorial".
  Some circuit examples can be found in "Clash.Examples".
-}

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE TypeOperators       #-}

{-# LANGUAGE Safe #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module Clash.Prelude.Safe
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
    -- * RAM primitives with a combinational read port
  , asyncRam
  , asyncRamPow2
    -- * BlockRAM primitives
  , blockRam
  , blockRamPow2
    -- ** BlockRAM read/write conflict resolution
  , readNew
    -- * Utility functions
  , isRising
  , isFalling
  , riseEvery
  , oscillate
    -- * Exported modules
    -- ** Synchronous signals
  , module Clash.Signal
  , module Clash.Signal.Delayed
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
    -- ** Type classes
    -- *** Clash
  , module Clash.Class.BitPack
  , module Clash.Class.Num
  , module Clash.Class.Resize
    -- *** Other
  , module Control.Applicative
  , module Data.Bits
      -- ** Exceptions
  , module Clash.XException
  , E.undefined
    -- ** Named types
  , module Clash.NamedTypes
    -- ** Haskell Prelude
    -- $hiding
  , module Prelude
  )
where

import           Control.Applicative
import           Data.Bits
import           GHC.TypeLits
import           GHC.TypeLits.Extra
import           Prelude hiding
  ((++), (!!), concat, drop, foldl, foldl1, foldr, foldr1, head, init, iterate,
   last, length, map, repeat, replicate, reverse, scanl, scanr, splitAt, tail,
   take, unzip, unzip3, zip, zip3, zipWith, zipWith3, undefined)

import           Clash.Annotations.TopEntity
import           Clash.Class.BitPack
import           Clash.Class.Num
import           Clash.Class.Resize
import           Clash.NamedTypes
import           Clash.Prelude.BitIndex
import           Clash.Prelude.BitReduction
import           Clash.Prelude.BlockRam
import qualified Clash.Explicit.Prelude.Safe as E
import           Clash.Prelude.Mealy         (mealy, mealyB, (<^>))
import           Clash.Prelude.Moore         (moore, mooreB)
import           Clash.Prelude.RAM           (asyncRam,asyncRamPow2)
import           Clash.Prelude.ROM           (asyncRom,asyncRomPow2,rom,romPow2)
import           Clash.Prelude.DataFlow
import           Clash.Promoted.Nat
import           Clash.Promoted.Nat.TH
import           Clash.Promoted.Nat.Literals
import           Clash.Sized.BitVector
import           Clash.Sized.Fixed
import           Clash.Sized.Index
import           Clash.Sized.RTree
import           Clash.Sized.Signed
import           Clash.Sized.Unsigned
import           Clash.Sized.Vector
import           Clash.Signal
import           Clash.Signal.Delayed
import           Clash.XException

{- $setup
>>> :set -XFlexibleContexts -XTypeApplications
>>> let rP = registerB (8,8)
-}

{- $hiding
"Clash.Prelude" re-exports most of the Haskell "Prelude" with the exception of
the following: (++), (!!), concat, drop, foldl, foldl1, foldr, foldr1, head,
init, iterate, last, length, map, repeat, replicate, reverse, scanl, scanr,
splitAt, tail, take, unzip, unzip3, zip, zip3, zipWith, zipWith3.

It instead exports the identically named functions defined in terms of
'Clash.Sized.Vector.Vec' at "Clash.Sized.Vector".
-}

-- | Create a 'register' function for product-type like signals (e.g. '(Signal a, Signal b)')
--
-- > rP :: HiddenClockReset domain
-- >    => (Signal domain Int, Signal domain Int)
-- >    -> (Signal domain Int, Signal domain Int)
-- > rP = registerB (8,8)
--
-- >>> simulateB rP [(1,1),(2,2),(3,3)] :: [(Int,Int)]
-- [(8,8),(1,1),(2,2),(3,3)...
-- ...
registerB
  :: (HiddenClockReset domain, Bundle a)
  => a
  -> Unbundled domain a
  -> Unbundled domain a
registerB = hideClockReset E.registerB
infixr 3 `registerB`
{-# INLINE registerB #-}

-- | Give a pulse when the 'Signal' goes from 'minBound' to 'maxBound'
isRising
  :: (HiddenClockReset domain, Bounded a, Eq a)
  => a -- ^ Starting value
  -> Signal domain a
  -> Signal domain Bool
isRising = hideClockReset E.isRising
{-# INLINE isRising #-}

-- | Give a pulse when the 'Signal' goes from 'maxBound' to 'minBound'
isFalling
  :: (HiddenClockReset domain, Bounded a, Eq a)
  => a -- ^ Starting value
  -> Signal domain a
  -> Signal domain Bool
isFalling = hideClockReset E.isFalling
{-# INLINE isFalling #-}

-- | Give a pulse every @n@ clock cycles. This is a useful helper function when
-- combined with functions like @'Clash.Signal.regEn'@ or @'Clash.Signal.mux'@,
-- in order to delay a register by a known amount.
--
-- To be precise: the given signal will be @'False'@ for the next @n-1@ cycles,
-- followed by a single @'True'@ value:
--
-- >>> Prelude.last (sampleN 1024 (riseEvery d1024)) == True
-- True
-- >>> Prelude.or (sampleN 1023 (riseEvery d1024)) == False
-- True
--
-- For example, to update a counter once every 10 million cycles:
--
-- @
-- counter = 'Clash.Signal.regEn' 0 ('riseEvery' ('SNat' :: 'SNat' 10000000)) (counter + 1)
-- @
riseEvery
  :: HiddenClockReset domain
  => SNat n
  -> Signal domain Bool
riseEvery = hideClockReset E.riseEvery
{-# INLINE riseEvery #-}

-- | Oscillate a @'Bool'@ for a given number of cycles. This is a convenient
-- function when combined with something like @'regEn'@, as it allows you to
-- easily hold a register value for a given number of cycles. The input @'Bool'@
-- determines what the initial value is.
--
-- To oscillate on an interval of 5 cycles:
--
-- >>> sampleN 10 (oscillate False d5)
-- [False,False,False,False,False,True,True,True,True,True]
--
-- To oscillate between @'True'@ and @'False'@:
--
-- >>> sampleN 10 (oscillate False d1)
-- [False,True,False,True,False,True,False,True,False,True]
--
-- An alternative definition for the above could be:
--
-- >>> let osc' = register False (not <$> osc')
-- >>> let sample' = sampleN 200
-- >>> sample' (oscillate False d1) == sample' osc'
-- True
oscillate
  :: HiddenClockReset domain
  => Bool
  -> SNat n
  -> Signal domain Bool
oscillate = hideClockReset E.oscillate
{-# INLINE oscillate #-}
