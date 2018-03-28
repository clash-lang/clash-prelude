{-|
Copyright  :  (C) 2015-2016, University of Twente,
                  2017     , Myrtle Software Ltd, Google Inc.
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

= Initialising a BlockRAM with a data file #usingramfiles#

BlockRAM primitives that can be initialised with a data file. The BNF grammar
for this data file is simple:

@
FILE = LINE+
LINE = BIT+
BIT  = '0'
     | '1'
@

Consecutive @LINE@s correspond to consecutive memory addresses starting at @0@.
For example, a data file @memory.bin@ containing the 9-bit unsigned number
@7@ to @13@ looks like:

@
000000111
000001000
000001001
000001010
000001011
000001100
000001101
@

We can instantiate a BlockRAM using the content of the above file like so:

@
f :: HiddenClock domain -> Signal domain (Unsigned 3) -> Signal domain (Unsigned 9)
f rd = 'Clash.Class.BitPack.unpack' '<$>' exposeClock 'blockRamFile' clk d7 \"memory.bin\" rd (signal Nothing)
@

In the example above, we basically treat the BlockRAM as an synchronous ROM.
We can see that it works as expected:

@
__>>> import qualified Data.List as L__
__>>> L.tail $ sampleN 4 $ f (fromList [3..5])__
[10,11,12]
@

However, we can also interpret the same data as a tuple of a 6-bit unsigned
number, and a 3-bit signed number:

@
g :: HiddenClock domain -> Signal domain (Unsigned 3) -> Signal domain (Unsigned 6,Signed 3)
g clk rd = 'Clash.Class.BitPack.unpack' '<$>' exposeClock 'blockRamFile' clk d7 \"memory.bin\" rd (signal Nothing)
@

And then we would see:

@
__>>> import qualified Data.List as L__
__>>> L.tail $ sampleN 4 $ g (fromList [3..5])__
[(1,2),(1,3)(1,-4)]
@

-}

{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

{-# LANGUAGE Unsafe #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module Clash.Prelude.BlockRam.File
  ( -- * BlockRAM synchronised to an arbitrary clock
    blockRamFile
  , blockRamFilePow2
  )
where

import GHC.TypeLits                           (KnownNat)
import GHC.Stack                              (HasCallStack, withFrozenCallStack)


import qualified Clash.Explicit.BlockRam.File as E
import           Clash.Promoted.Nat           (SNat)
import           Clash.Signal                 (HiddenClock, Signal, hideClock)
import           Clash.Sized.BitVector        (BitVector)
import           Clash.Sized.Unsigned         (Unsigned)

-- | Create a blockRAM with space for 2^@n@ elements
--
-- * __NB__: Read value is delayed by 1 cycle
-- * __NB__: Initial output value is 'undefined'
-- * __NB__: This function might not work for specific combinations of
-- code-generation backends and hardware targets. Please check the support table
-- below:
--
--     @
--                    | VHDL     | Verilog  | SystemVerilog |
--     ===============+==========+==========+===============+
--     Altera/Quartus | Broken   | Works    | Works         |
--     Xilinx/ISE     | Works    | Works    | Works         |
--     ASIC           | Untested | Untested | Untested      |
--     ===============+==========+==========+===============+
--     @
--
-- Additional helpful information:
--
-- * See "Clash.Prelude.BlockRam#usingrams" for more information on how to use a
-- Block RAM.
-- * Use the adapter 'readNew'' for obtaining write-before-read semantics like this: @readNew' clk (blockRamFilePow2' clk file) rd wrM@.
-- * See "Clash.Prelude.BlockRam.File#usingramfiles" for more information on how
-- to instantiate a Block RAM with the contents of a data file.
-- * See "Clash.Sized.Fixed#creatingdatafiles" for ideas on how to create your
-- own data files.
blockRamFilePow2
  :: forall domain n m
   . (KnownNat m, KnownNat n, HiddenClock domain, HasCallStack)
  => FilePath
  -- ^ File describing the initial content of the blockRAM
  -> Signal domain (Unsigned n)
  -- ^ Read address @r@
  -> Signal domain (Maybe (Unsigned n, BitVector m))
  -- ^ (write address @w@, value to write)
  -> Signal domain (BitVector m)
  -- ^ Value of the @blockRAM@ at address @r@ from the previous
  -- clock cycle
blockRamFilePow2 = \fp rd wrM -> withFrozenCallStack
  (hideClock E.blockRamFilePow2 fp rd wrM)
{-# INLINE blockRamFilePow2 #-}

-- | Create a blockRAM with space for @n@ elements
--
-- * __NB__: Read value is delayed by 1 cycle
-- * __NB__: Initial output value is 'undefined'
-- * __NB__: This function might not work for specific combinations of
-- code-generation backends and hardware targets. Please check the support table
-- below:
--
--     @
--                    | VHDL     | Verilog  | SystemVerilog |
--     ===============+==========+==========+===============+
--     Altera/Quartus | Broken   | Works    | Works         |
--     Xilinx/ISE     | Works    | Works    | Works         |
--     ASIC           | Untested | Untested | Untested      |
--     ===============+==========+==========+===============+
--     @
--
-- Additional helpful information:
--
-- * See "Clash.Prelude.BlockRam#usingrams" for more information on how to use a
-- Block RAM.
-- * Use the adapter 'readNew'' for obtaining write-before-read semantics like this: @readNew' clk (blockRamFile' clk size file) rd wrM@.
-- * See "Clash.Prelude.BlockRam.File#usingramfiles" for more information on how
-- to instantiate a Block RAM with the contents of a data file.
-- * See "Clash.Sized.Fixed#creatingdatafiles" for ideas on how to create your
-- own data files.
blockRamFile
  :: (KnownNat m, Enum addr, HiddenClock domain, HasCallStack)
  => SNat n
  -- ^ Size of the blockRAM
  -> FilePath
  -- ^ File describing the initial content of the blockRAM
  -> Signal domain addr
  -- ^ Read address @r@
  -> Signal domain (Maybe (addr, BitVector m))
  -- ^ (write address @w@, value to write)
  -> Signal domain (BitVector m)
  -- ^ Value of the @blockRAM@ at address @r@ from the previous
  -- clock cycle
blockRamFile = \sz fp rd wrM -> withFrozenCallStack
  (hideClock E.blockRamFile sz fp rd wrM)
{-# INLINE blockRamFile #-}
