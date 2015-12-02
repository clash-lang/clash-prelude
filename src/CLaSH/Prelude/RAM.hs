{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

{-# LANGUAGE Safe #-}

-- See: https://github.com/clash-lang/clash-compiler/commit/721fcfa9198925661cd836668705f817bddaae3c
-- as to why we need this.
#if __GLASGOW_HASKELL__ > 711
{-# OPTIONS_GHC -fno-cpr-anal #-}
#endif

{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Copyright  :  (C) 2015, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

RAM primitives with a combinational read port.
-}
module CLaSH.Prelude.RAM
  ( -- * RAM synchronised to an arbitrary clock
    asyncRam
  , asyncRamPow2
    -- * Internal
  , asyncRam#
  )
where

import Control.Monad          (when)
import Control.Monad.ST.Lazy  (ST,runST)
import Data.Array.MArray.Safe (newArray_,readArray,writeArray)
import Data.Array.ST.Safe     (STArray)
import GHC.TypeLits           (KnownNat, type (^))

import CLaSH.Promoted.Nat     (SNat,snat,snatToInteger)
import CLaSH.Signal.Bundle    (bundle')
import CLaSH.Signal.Explicit  (Signal', SClock, unsafeSynchronizer)
import CLaSH.Sized.Unsigned   (Unsigned)

{-# INLINE asyncRamPow2 #-}
-- | Create a RAM with space for 2^@n@ elements
--
-- * __NB__: Initial content of the RAM is 'undefined'
--
-- Additional helpful information:
--
-- * See "CLaSH.Prelude.BlockRam#usingrams" for more information on how to use a
-- RAM.
asyncRamPow2 :: forall wclk rclk n a .
                (KnownNat n, KnownNat (2^n))
             => (?wclk :: SClock wclk)    -- ^ 'Clock' to which to synchronise
                                          -- the write port of the RAM
             => (?rclk :: SClock rclk)    -- ^ 'Clock' to which the read
                                          -- address signal, @r@, is
                                          -- synchronised
             => Signal' wclk (Unsigned n) -- ^ Write address @w@
             -> Signal' rclk (Unsigned n) -- ^ Read address @r@
             -> Signal' wclk Bool         -- ^ Write enable
             -> Signal' wclk a            -- ^ Value to write (at address @w@)
             -> Signal' rclk a
             -- ^ Value of the @RAM@ at address @r@
asyncRamPow2 = asyncRam (snat :: SNat (2^n))

{-# INLINE asyncRam #-}
-- | Create a RAM with space for @n@ elements
--
-- * __NB__: Initial content of the RAM is 'undefined'
--
-- Additional helpful information:
--
-- * See "CLaSH.Prelude.BlockRam#usingrams" for more information on how to use a
-- RAM.
asyncRam :: Enum addr
         => (?wclk :: SClock wclk) -- ^ 'Clock' to which to synchronise the write
                                   -- port of the RAM
         => (?rclk :: SClock rclk) -- ^ 'Clock' to which the read address signal,
                                   -- @r@, is synchronised
         => SNat n                 -- ^ Size @n@ of the RAM
         -> Signal' wclk addr      -- ^ Write address @w@
         -> Signal' rclk addr      -- ^ Read address @r@
         -> Signal' wclk Bool      -- ^ Write enable
         -> Signal' wclk a         -- ^ Value to write (at address @w@)
         -> Signal' rclk a         -- ^ Value of the @RAM@ at address @r@
asyncRam sz wr rd en din = asyncRam# ?wclk ?rclk sz (fromEnum <$> wr)
                                     (fromEnum <$> rd) en din

{-# NOINLINE asyncRam# #-}
-- | RAM primitive
asyncRam# :: SClock wclk       -- ^ 'Clock' to which to synchronise the write
                               -- port of the RAM
          -> SClock rclk       -- ^ 'Clock' to which the read address signal,
                               -- @r@, is synchronised
          -> SNat n            -- ^ Size @n@ of the RAM
          -> Signal' wclk Int  -- ^ Write address @w@
          -> Signal' rclk Int  -- ^ Read address @r@
          -> Signal' wclk Bool -- ^ Write enable
          -> Signal' wclk a    -- ^ Value to write (at address @w@)
          -> Signal' rclk a    -- ^ Value of the @RAM@ at address @r@
asyncRam# wclk rclk sz wr rd en din = let ?clk1 = wclk; ?clk2 = rclk; in unsafeSynchronizer dout
  where
    szI  = fromInteger $ snatToInteger sz
    rd'  = let ?clk1 = rclk; ?clk2 = wclk; in unsafeSynchronizer rd
    dout = runST $ do
      arr <- newArray_ (0,szI-1)
      traverse (ramT arr) (bundle' wclk (wr,rd',en,din))

    ramT :: STArray s Int e -> (Int,Int,Bool,e) -> ST s e
    ramT ram (w,r,e,d) = do
      d' <- readArray ram r
      when e (writeArray ram w d)
      return d'
