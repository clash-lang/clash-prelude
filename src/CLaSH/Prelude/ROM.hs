{-|
Copyright  :  (C) 2015-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

ROMs
-}

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE ImplicitParams   #-}
{-# LANGUAGE MagicHash        #-}
{-# LANGUAGE TypeOperators    #-}

{-# LANGUAGE Safe #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_HADDOCK show-extensions #-}

module CLaSH.Prelude.ROM
  ( -- * Asynchronous ROM
    asyncRom
  , asyncRomPow2
    -- * Synchronous ROM synchronised to the system clock
  , rom
  , romPow2
    -- * Synchronous ROM synchronised to an arbitrary clock
  , rom#
  , romPow2#
    -- * Internal
  , asyncRom#
  , rom##
  )
where

import Data.Array             ((!),listArray)
import GHC.Stack              (HasCallStack, withFrozenCallStack)
import GHC.TypeLits           (KnownNat, type (^))

import CLaSH.Signal           (Signal, Clock, ClockKind (..))
import CLaSH.Sized.Unsigned   (Unsigned)
import CLaSH.Signal.Explicit  (delay#)
import CLaSH.Sized.Vector     (Vec, maxIndex, toList)

{-# INLINE asyncRom #-}
-- | An asynchronous/combinational ROM with space for @n@ elements
--
-- Additional helpful information:
--
-- * See "CLaSH.Sized.Fixed#creatingdatafiles" and "CLaSH.Prelude.BlockRam#usingrams"
-- for ideas on how to use ROMs and RAMs
asyncRom :: (KnownNat n, Enum addr)
         => Vec n a -- ^ ROM content
                    --
                    -- __NB:__ must be a constant
         -> addr    -- ^ Read address @rd@
         -> a       -- ^ The value of the ROM at address @rd@
asyncRom content rd = asyncRom# content (fromEnum rd)

{-# INLINE asyncRomPow2 #-}
-- | An asynchronous/combinational ROM with space for 2^@n@ elements
--
-- Additional helpful information:
--
-- * See "CLaSH.Sized.Fixed#creatingdatafiles" and "CLaSH.Prelude.BlockRam#usingrams"
-- for ideas on how to use ROMs and RAMs
asyncRomPow2 :: KnownNat n
             => Vec (2^n) a -- ^ ROM content
                            --
                            -- __NB:__ must be a constant
             -> Unsigned n  -- ^ Read address @rd@
             -> a           -- ^ The value of the ROM at address @rd@
asyncRomPow2 = asyncRom

{-# NOINLINE asyncRom# #-}
-- | asyncROM primitive
asyncRom# :: KnownNat n
          => Vec n a  -- ^ ROM content
                      --
                      -- __NB:__ must be a constant
          -> Int      -- ^ Read address @rd@
          -> a        -- ^ The value of the ROM at address @rd@
asyncRom# content rd = arr ! rd
  where
    szI = maxIndex content
    arr = listArray (0,szI) (toList content)

{-# INLINE rom #-}
-- | A ROM with a synchronous read port, with space for @n@ elements
--
-- * __NB__: Read value is delayed by 1 cycle
-- * __NB__: Initial output value is 'undefined'
--
-- Additional helpful information:
--
-- * See "CLaSH.Sized.Fixed#creatingdatafiles" and "CLaSH.Prelude.BlockRam#usingrams"
-- for ideas on how to use ROMs and RAMs
rom :: (HasCallStack, KnownNat n, KnownNat m, ?clk :: Clock 'Original domain)
    => Vec n a               -- ^ ROM content
                             --
                             -- __NB:__ must be a constant
    -> Signal domain (Unsigned m)   -- ^ Read address @rd@
    -> Signal domain a              -- ^ The value of the ROM at address @rd@
rom = rom# ?clk

{-# INLINE romPow2 #-}
-- | A ROM with a synchronous read port, with space for 2^@n@ elements
--
-- * __NB__: Read value is delayed by 1 cycle
-- * __NB__: Initial output value is 'undefined'
--
-- Additional helpful information:
--
-- * See "CLaSH.Sized.Fixed#creatingdatafiles" and "CLaSH.Prelude.BlockRam#usingrams"
-- for ideas on how to use ROMs and RAMs
romPow2 :: (HasCallStack, KnownNat n, ?clk :: Clock 'Original domain)
        => Vec (2^n) a         -- ^ ROM content
                               --
                               -- __NB:__ must be a constant
        -> Signal domain (Unsigned n) -- ^ Read address @rd@
        -> Signal domain a            -- ^ The value of the ROM at address @rd@
romPow2 = rom# ?clk

{-# INLINE romPow2# #-}
-- | A ROM with a synchronous read port, with space for 2^@n@ elements
--
-- * __NB__: Read value is delayed by 1 cycle
-- * __NB__: Initial output value is 'undefined'
--
-- Additional helpful information:
--
-- * See "CLaSH.Sized.Fixed#creatingdatafiles" and "CLaSH.Prelude.BlockRam#usingrams"
-- for ideas on how to use ROMs and RAMs
romPow2# :: (HasCallStack, KnownNat n)
         => Clock clk domain               -- ^ 'Clock' to synchronize to
         -> Vec (2^n) a              -- ^ ROM content
                                     --
                                     -- __NB:__ must be a constant
         -> Signal domain (Unsigned n) -- ^ Read address @rd@
         -> Signal domain a            -- ^ The value of the ROM at address @rd@
romPow2# = rom#

{-# INLINE rom# #-}
-- | A ROM with a synchronous read port, with space for @n@ elements
--
-- * __NB__: Read value is delayed by 1 cycle
-- * __NB__: Initial output value is 'undefined'
--
-- Additional helpful information:
--
-- * See "CLaSH.Sized.Fixed#creatingdatafiles" and "CLaSH.Prelude.BlockRam#usingrams"
-- for ideas on how to use ROMs and RAMs
rom# :: (HasCallStack, KnownNat n, Enum addr)
     => Clock clk domain -- ^ 'Clock' to synchronize to
     -> Vec n a          -- ^ ROM content
                         --
                         -- __NB:__ must be a constant
     -> Signal domain addr -- ^ Read address @rd@
     -> Signal domain a
     -- ^ The value of the ROM at address @rd@ from the previous clock cycle
rom# clk content rd = (withFrozenCallStack rom#) clk content (fromEnum <$> rd)

{-# NOINLINE rom## #-}
-- | ROM primitive
rom## :: (HasCallStack, KnownNat n)
      => Clock clk domain -- ^ 'Clock' to synchronize to
      -> Vec n a          -- ^ ROM content
                          --
                          -- __NB:__ must be a constant
      -> Signal domain Int  -- ^ Read address @rd@
      -> Signal domain a
      -- ^ The value of the ROM at address @rd@ from the previous clock cycle
rom## clk content rd = (withFrozenCallStack delay#) clk ((arr !) <$> rd)
  where
    szI = maxIndex content
    arr = listArray (0,szI) (toList content)
