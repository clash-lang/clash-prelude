{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

{-# LANGUAGE Safe #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}
{-# OPTIONS_HADDOCK show-extensions #-}

{-|
Copyright   :  (C) 2015, University of Twente
License     :  BSD2 (see the file LICENSE)
Maintainer  :  Christiaan Baaij <christiaan.baaij@gmail.com>

Synchronizer circuits for safe clock domain crossings
-}
module CLaSH.Prelude.Synchronizer
  ( -- * Bit-synchronizers
    dualFlipFlopSynchronizer
    -- * Word-synchronizers
  , asyncFIFOSynchronizer
  )
where

import Data.Bits                   (complement, shiftR, xor)
import GHC.TypeLits                (KnownNat, type (+))

import CLaSH.Class.BitPack         (pack)
import CLaSH.Class.Resize          (zeroExtend)
import CLaSH.Prelude.BitIndex      (slice)
import CLaSH.Prelude.Mealy         (mealyB)
import CLaSH.Prelude.RAM           (asyncRam)
import CLaSH.Promoted.Nat          (SNat, powSNat, subSNat)
import CLaSH.Promoted.Nat.Literals (d0, d1, d2)
import CLaSH.Signal                ((.&&.), not1)
import CLaSH.Signal.Explicit       (Signal', SClock, register,
                                    unsafeSynchronizer)
import CLaSH.Sized.BitVector       (BitVector, (++#))

-- * Dual flip-flop synchronizer

-- | Synchroniser based on two sequentially connected flip-flops.
--
--  * __NB__: This synchroniser can be used for __bit__-synchronization.
--
--  * __NB__: Although this synchroniser does reduce metastability, it does
--  not guarantee the proper synchronisation of a whole __word__. For
--  example, given that the output is sampled twice as fast as the input is
--  running, and we have two samples in the input stream that look like:
--
--      @[0111,1000]@
--
--      But the circuit driving the input stream has a longer propagation delay
--      on __msb__ compared to the __lsb__s. What can happen is an output stream
--      that looks like this:
--
--      @[0111,0111,0000,1000]@
--
--      Where the level-change of the __msb__ was not captured, but the level
--      change of the __lsb__s were.
--
--      If you want to have /safe/ __word__-synchronisation use
--      'asyncFIFOSynchronizer'.
dualFlipFlopSynchronizer :: (?clk1 :: SClock clk1) -- ^ 'Clock' to which the incoming
                                                   -- data is synchronised
                         => (?clk2 :: SClock clk2) -- ^ 'Clock' to which the outgoing
                                                   -- data is synchronised
                         => a                      -- ^ Initial value of the two
                                                   -- synchronisation registers
                         -> Signal' clk1 a         -- ^ Incoming data
                         -> Signal' clk2 a         -- ^ Outgoing, synchronised, data
dualFlipFlopSynchronizer i = register i
                           . register i
                           . unsafeSynchronizer
  where ?clk = ?clk2

-- * Asynchronous FIFO synchronizer

fifoMem :: _
        => (?wclk :: SClock wclk)
        => (?rclk :: SClock rclk)
        => SNat addrSize
        -> Signal' wclk (BitVector addrSize)
        -> Signal' rclk (BitVector addrSize)
        -> Signal' wclk Bool
        -> Signal' wclk Bool
        -> Signal' wclk a
        -> Signal' rclk a
fifoMem addrSize waddr raddr winc wfull wdata =
  asyncRam (d2 `powSNat` addrSize)
           waddr raddr
           (winc .&&. not1 wfull)
           wdata

boolToBV :: (KnownNat n, KnownNat (n+1)) => Bool -> BitVector (n + 1)
boolToBV = zeroExtend . pack

ptrCompareT :: _
            => SNat addrSize
            -> (BitVector (addrSize + 1) -> BitVector (addrSize + 1) -> Bool)
            -> (BitVector (addrSize + 1), BitVector (addrSize + 1), Bool)
            -> (BitVector (addrSize + 1), Bool)
            -> ((BitVector (addrSize + 1), BitVector (addrSize + 1), Bool)
               ,(Bool, BitVector addrSize, BitVector (addrSize + 1)))
ptrCompareT addrSize flagGen (bin,ptr,flag) (s_ptr,inc) = ((bin',ptr',flag')
                                                          ,(flag,addr,ptr))
  where
    -- GRAYSTYLE2 pointer
    bin' = bin + boolToBV (inc && not flag)
    ptr' = (bin' `shiftR` 1) `xor` bin'
    addr = slice (addrSize `subSNat` d1) d0 bin

    flag' = flagGen ptr' s_ptr


-- FIFO full: when next pntr == synchonized {~wptr[addrSize:addrSize-1],wptr[addrSize-1:0]}
isFull :: _
       => SNat addrSize
       -> BitVector (addrSize + 1)
       -> BitVector (addrSize + 1)
       -> Bool
isFull addrSize ptr s_ptr =
  ptr == (complement (slice addrSize (addrSize `subSNat` d1) s_ptr) ++#
         slice (addrSize `subSNat` d2) d0 s_ptr)

-- | Synchroniser implemented as a FIFO around an asynchronous RAM. Based on the
-- design described in "CLaSH.Tutorial#multiclock", which is itself based on the
-- design described in <http://www.sunburst-design.com/papers/CummingsSNUG2002SJ_FIFO1.pdf>.
--
-- __NB__: This synchroniser can be used for __word__-synchronization.
asyncFIFOSynchronizer :: _
                      => SNat addrSize     -- ^ Size of the internally used
                                           -- addresses, the FIFO contains
                                           -- @2^addrSize@ elements.
                      -> SClock wclk       -- ^ 'Clock' to which the write port
                                           -- is synchronised
                      -> SClock rclk       -- ^ 'Clock' to which the read port
                                           -- is synchronised
                      -> Signal' wclk a    -- ^ Element to insert
                      -> Signal' wclk Bool -- ^ Write request
                      -> Signal' rclk Bool -- ^ Read request
                      -> (Signal' rclk a, Signal' rclk Bool, Signal' wclk Bool)
                      -- ^ (Oldest element in the FIFO, @empty@ flag, @full@ flag)
asyncFIFOSynchronizer addrSize wclk rclk wdata winc rinc = (rdata,rempty,wfull)
  where
    s_rptr = let ?clk1 = rclk; ?clk2 = wclk; in dualFlipFlopSynchronizer 0 rptr
    s_wptr = let ?clk1 = wclk; ?clk2 = rclk; in dualFlipFlopSynchronizer 0 wptr

    rdata = fifoMem addrSize waddr raddr winc wfull wdata
      where ?wclk = wclk
            ?rclk = rclk

    (rempty,raddr,rptr) = mealyB (ptrCompareT addrSize (==)) (0,0,True)
                                 (s_wptr,rinc)
      where ?clk = rclk

    (wfull,waddr,wptr)  = mealyB (ptrCompareT addrSize (isFull addrSize))
                                 (0,0,False) (s_rptr,winc)
      where ?clk = wclk
