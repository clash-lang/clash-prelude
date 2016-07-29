{-|
Copyright  :  (C) 2015-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

RAM primitives with a combinational read port.
-}

{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE TypeApplications    #-}

{-# LANGUAGE Safe #-}

-- See: https://github.com/clash-lang/clash-compiler/commit/721fcfa9198925661cd836668705f817bddaae3c
-- as to why we need this.
{-# OPTIONS_GHC -fno-cpr-anal #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module CLaSH.Prelude.RAM
  ( -- * RAM synchronised to the system clock
    asyncRam
  , asyncRamPow2
    -- * RAM synchronised to an arbitrary clock
  , asyncRam#
  , asyncRamPow2#
    -- * Internal
  , asyncRam##
  )
where

import Control.Monad          (when)
import Control.Monad.ST.Lazy  (ST,runST)
import Data.Array.MArray.Safe (newArray_,readArray,writeArray)
import Data.Array.ST.Safe     (STArray)
import GHC.TypeLits           (KnownNat)

import CLaSH.Promoted.Nat     (SNat (..), snatToInteger, pow2SNat)
import CLaSH.Signal           (Signal,Clock)
import CLaSH.Signal.Bundle    (bundle)
import CLaSH.Signal.Explicit  (unsafeSynchronizer)
import CLaSH.Sized.Unsigned   (Unsigned)

{-# INLINE asyncRam #-}
-- | Create a RAM with space for @n@ elements.
--
-- * __NB__: Initial content of the RAM is 'undefined'
--
-- Additional helpful information:
--
-- * See "CLaSH.Prelude.BlockRam#usingrams" for more information on how to use a
-- RAM.
asyncRam :: (Enum addr, ?clk :: Clock clk domain)
         => SNat n             -- ^ Size @n@ of the RAM
         -> Signal domain addr -- ^ Write address @w@
         -> Signal domain addr -- ^ Read address @r@
         -> Signal domain Bool -- ^ Write enable
         -> Signal domain a    -- ^ Value to write (at address @w@)
         -> Signal domain a    -- ^ Value of the @RAM@ at address @r@
asyncRam = asyncRam# ?clk ?clk

{-# INLINE asyncRamPow2 #-}
-- | Create a RAM with space for 2^@n@ elements
--
-- * __NB__: Initial content of the RAM is 'undefined'
--
-- Additional helpful information:
--
-- * See "CLaSH.Prelude.BlockRam#usingrams" for more information on how to use a
-- RAM.
asyncRamPow2 :: (KnownNat n, ?clk :: Clock clk domain)
             => Signal domain (Unsigned n) -- ^ Write address @w@
             -> Signal domain (Unsigned n) -- ^ Read address @r@
             -> Signal domain Bool         -- ^ Write enable
             -> Signal domain a            -- ^ Value to write (at address @w@)
             -> Signal domain a            -- ^ Value of the @RAM@ at address @r@
asyncRamPow2 = asyncRamPow2# ?clk ?clk

{-# INLINE asyncRamPow2# #-}
-- | Create a RAM with space for 2^@n@ elements
--
-- * __NB__: Initial content of the RAM is 'undefined'
--
-- Additional helpful information:
--
-- * See "CLaSH.Prelude.BlockRam#usingrams" for more information on how to use a
-- RAM.
asyncRamPow2# :: forall wdom rdom wclk rclk n a .
                 KnownNat n
              => Clock wclk wdom          -- ^ 'Clock' to which to synchronise
                                          -- the write port of the RAM
              -> Clock rclk rdom          -- ^ 'Clock' to which the read
                                          -- address signal, @r@, is
                                          -- synchronised
              -> Signal wdom (Unsigned n) -- ^ Write address @w@
              -> Signal rdom (Unsigned n) -- ^ Read address @r@
              -> Signal wdom Bool         -- ^ Write enable
              -> Signal wdom a            -- ^ Value to write (at address @w@)
              -> Signal rdom a
              -- ^ Value of the @RAM@ at address @r@
asyncRamPow2# wclk rclk = asyncRam# wclk rclk (pow2SNat (SNat @ n))

{-# INLINE asyncRam# #-}
-- | Create a RAM with space for @n@ elements
--
-- * __NB__: Initial content of the RAM is 'undefined'
--
-- Additional helpful information:
--
-- * See "CLaSH.Prelude.BlockRam#usingrams" for more information on how to use a
-- RAM.
asyncRam# :: Enum addr
          => Clock wclk wdom  -- ^ 'Clock' to which to synchronise the write
                              -- port of the RAM
          -> Clock rclk rdom  -- ^ 'Clock' to which the read address signal,
                              -- @r@, is synchronised
          -> SNat n           -- ^ Size @n@ of the RAM
          -> Signal wdom addr -- ^ Write address @w@
          -> Signal rdom addr -- ^ Read address @r@
          -> Signal wdom Bool -- ^ Write enable
          -> Signal wdom a    -- ^ Value to write (at address @w@)
          -> Signal rdom a    -- ^ Value of the @RAM@ at address @r@
asyncRam# wclk rclk sz wr rd en din = asyncRam## wclk rclk sz (fromEnum <$> wr)
                                                 (fromEnum <$> rd) en din

{-# NOINLINE asyncRam## #-}
-- | RAM primitive
asyncRam## :: Clock wclk wdom  -- ^ 'Clock' to which to synchronise the write
                               -- port of the RAM
           -> Clock rclk rdom
           -> SNat n           -- ^ Size @n@ of the RAM
           -> Signal wdom Int  -- ^ Write address @w@
           -> Signal rdom Int  -- ^ Read address @r@
           -> Signal wdom Bool -- ^ Write enable
           -> Signal wdom a    -- ^ Value to write (at address @w@)
           -> Signal rdom a    -- ^ Value of the @RAM@ at address @r@
asyncRam## wclk rclk sz wr rd en din = unsafeSynchronizer wclk rclk dout
  where
    szI  = fromInteger $ snatToInteger sz
    rd'  = unsafeSynchronizer rclk wclk rd
    dout = runST $ do
      arr <- newArray_ (0,szI-1)
      traverse (ramT arr) (bundle (wr,rd',en,din))

    ramT :: STArray s Int e -> (Int,Int,Bool,e) -> ST s e
    ramT ram (w,r,e,d) = do
      d' <- readArray ram r
      when e (writeArray ram w d)
      return d'
