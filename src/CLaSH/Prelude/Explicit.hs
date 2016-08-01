{-|
Copyright  :  (C) 2013-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

This module defines the explicitly clocked counterparts of the functions
defined in "CLaSH.Prelude".

This module uses the explicitly clocked 'Signal'' synchronous signals, as
opposed to the implicitly clocked 'Signal' used in "CLaSH.Prelude". Take a
look at "CLaSH.Signal.Explicit" to see how you can make multi-clock designs
using explicitly clocked signals.
-}

{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE MagicHash     #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE Unsafe #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_HADDOCK show-extensions #-}

module CLaSH.Prelude.Explicit
  ( -- * Creating synchronous sequential circuits
    mealy#
  , mealyB#
  , moore#
  , mooreB#
  , registerB#
    -- * Synchronizer circuits for safe clock domain crossings
  , dualFlipFlopSynchronizer
  , asyncFIFOSynchronizer
    -- * ROMs
  , rom#
  , romPow2#
    -- ** ROMs initialised with a data file
  , romFile#
  , romFilePow2#
    -- * RAM primitives with a combinational read port
  , asyncRam#
  , asyncRamPow2#
    -- * BlockRAM primitives
  , blockRam#
  , blockRamPow2#
    -- ** BlockRAM primitives initialised with a data file
  , blockRamFile#
  , blockRamFilePow2#
    -- ** BlockRAM read/write conflict resolution
  , readNew#
    -- * Utility functions
  , window#
  , windowD#
  , isRising#
  , isFalling#
    -- * Testbench functions
  , assert#
  , stimuliGenerator#
  , outputVerifier#
    -- * Exported modules
    -- ** Explicitly clocked synchronous signals
  , module CLaSH.Signal.Explicit
  )
where

import Data.Default                 (Default (..))
import GHC.Stack                    (HasCallStack)
import GHC.TypeLits                 (KnownNat, type (+), natVal)
import Prelude                      hiding (repeat)

import CLaSH.Prelude.Explicit.Safe
import CLaSH.Prelude.BlockRam.File (blockRamFile#, blockRamFilePow2#)
import CLaSH.Prelude.ROM.File      (romFile#, romFilePow2#)
import CLaSH.Prelude.Testbench     (assert#, stimuliGenerator#, outputVerifier#)
import CLaSH.Signal                (Signal)
import CLaSH.Signal.Explicit
import CLaSH.Sized.Vector          (Vec (..), (+>>), asNatProxy, repeat)

{- $setup
>>> :set -XDataKinds -XMagicHash -XTypeApplications
>>> import CLaSH.Prelude
>>> import qualified Data.List as L
>>> type DomA = 'Domain "A" 100
>>> let clkA = Clock @DomA (signal True)
>>> let rstA = unsafeToAsyncReset# @DomA (fromList (False : L.repeat True))
>>> let window4 = window# rstA clkA :: Signal DomA Int -> Vec 4 (Signal DomA Int)
>>> let windowD3 = windowD# rstA clkA :: Signal DomA Int -> Vec 3 (Signal DomA Int)
-}

{-# INLINABLE window# #-}
-- | Give a window over a 'Signal''
--
-- @
-- type ClkA = 'Clk' \"A\" 100
--
-- clkA :: 'SClock' ClkA
-- clkA = 'sclock'
--
-- window4 :: 'Signal'' ClkA Int -> 'Vec' 4 ('Signal'' ClkA Int)
-- window4 = 'window'' clkA
-- @
--
-- >>> simulateB# window4 [1::Int,2,3,4,5] :: [Vec 4 Int]
-- [<1,0,0,0>,<2,1,0,0>,<3,2,1,0>,<4,3,2,1>,<5,4,3,2>...
-- ...
window# :: (HasCallStack, KnownNat n, Default a)
        => Reset res dom
        -> Clock clk dom              -- ^ Clock to which the incoming
                                      -- signal is synchronized
        -> Signal dom a               -- ^ Signal to create a window over
        -> Vec (n + 1) (Signal dom a) -- ^ Window of at least size 1
window# res clk x = x :> prev
  where
    prev = case natVal (asNatProxy prev) of
             0 -> repeat def
             _ -> let next = x +>> prev
                  in  registerB# res clk (repeat def) next

{-# INLINABLE windowD# #-}
-- | Give a delayed window over a 'Signal''
--
-- @
-- type ClkA = 'Clk' \"A\" 100
--
-- clkA :: 'SClock' ClkA
-- clkA = 'sclock'
--
-- windowD3 :: 'Signal'' ClkA Int -> 'Vec' 3 ('Signal'' ClkA Int)
-- windowD3 = 'windowD'' clkA
-- @
--
-- >>> simulateB# windowD3 [1::Int,2,3,4] :: [Vec 3 Int]
-- [<0,0,0>,<1,0,0>,<2,1,0>,<3,2,1>,<4,3,2>...
-- ...
windowD# :: (HasCallStack, KnownNat n, Default a)
         => Reset res dom
         -> Clock clk dom              -- ^ Clock to which the incoming signal
                                       -- is synchronized
         -> Signal dom a               -- ^ Signal to create a window over
         -> Vec (n + 1) (Signal dom a) -- ^ Window of at least size 1
windowD# res clk x = prev
  where
    prev = registerB# res clk (repeat def) next
    next = x +>> prev
