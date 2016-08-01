{-|
Copyright  :  (C) 2013-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# LANGUAGE Unsafe #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module CLaSH.Prelude.Testbench
  ( -- * Testbench functions for circuits synchronised to the system slock
    assert
  , stimuliGenerator
  , outputVerifier
    -- * Testbench functions for circuits synchronised to arbitrary clocks
  , assert#
  , stimuliGenerator#
  , outputVerifier#
  )
where

import Debug.Trace           (trace)
import GHC.TypeLits          (KnownNat)
import Prelude               hiding ((!!))

import CLaSH.Signal          (Clock, Reset, Signal, fromList)
import CLaSH.Signal.Bundle   (unbundle)
import CLaSH.Signal.Explicit (register#)
import CLaSH.Sized.Index     (Index)
import CLaSH.Sized.Vector    (Vec, (!!), maxIndex)

{- $setup
>>> :set -XTemplateHaskell -XDataKinds -XMagicHash -XTypeApplications
>>> import CLaSH.Prelude
>>> let testInput = stimuliGenerator $(v [(1::Int),3..21])
>>> let expectedOutput = outputVerifier $(v ([70,99,2,3,4,5,7,8,9,10]::[Int]))
>>> import CLaSH.Prelude.Explicit
>>> import qualified Data.List as L
>>> type DomA = 'Domain "A" 100
>>> let clkA = Clock @DomA (signal True)
>>> let rstA = unsafeToAsyncReset# @DomA (fromList (False : L.repeat True))
>>> let testInput# = stimuliGenerator# rstA clkA $(v [(1::Int),3..21])
>>> let expectedOutput# = outputVerifier# rstA clkA $(v ([70,99,2,3,4,5,7,8,9,10]::[Int]))
-}

{-# INLINE assert #-}
-- | Compares the first two 'Signal's for equality and logs a warning when they
-- are not equal. The second 'Signal' is considered the expected value. This
-- function simply returns the third 'Signal' unaltered as its result. This
-- function is used by 'outputVerifier'.
--
--
-- __NB__: This function /can/ be used in synthesizable designs.
assert :: (Eq a,Show a, ?clk :: Clock clk domain)
       => String          -- ^ Additional message
       -> Signal domain a -- ^ Checked value
       -> Signal domain a -- ^ Expected value
       -> Signal domain b -- ^ Return value
       -> Signal domain b
assert = assert# ?clk

{-# INLINE stimuliGenerator #-}
-- | To be used as one of the functions to create the \"magical\" 'testInput'
-- value, which the CλaSH compiler looks for to create the stimulus generator
-- for the generated VHDL testbench.
--
-- Example:
--
-- @
-- testInput :: 'Signal' Int
-- testInput = 'stimuliGenerator' $('CLaSH.Sized.Vector.v' [(1::Int),3..21])
-- @
--
-- >>> sampleN 13 testInput
-- [1,3,5,7,9,11,13,15,17,19,21,21,21]
stimuliGenerator :: (KnownNat l, ?res :: Reset rst domain, ?clk :: Clock clk domain)
                 => Vec l a         -- ^ Samples to generate
                 -> Signal domain a -- ^ Signal of given samples
stimuliGenerator = stimuliGenerator# ?res ?clk

{-# INLINE outputVerifier #-}
-- | To be used as one of the functions to generate the \"magical\" 'expectedOutput'
-- function, which the CλaSH compiler looks for to create the signal verifier
-- for the generated VHDL testbench.
--
-- Example:
--
-- @
-- expectedOutput :: 'Signal' Int -> 'Signal' Bool
-- expectedOutput = 'outputVerifier' $('CLaSH.Sized.Vector.v' ([70,99,2,3,4,5,7,8,9,10]::[Int]))
-- @
--
-- >>> import qualified Data.List as List
-- >>> sampleN 12 (expectedOutput (fromList ([0..10] List.++ [10,10,10])))
-- <BLANKLINE>
-- cycle(system1000): 0, outputVerifier
-- expected value: 70, not equal to actual value: 0
-- [False
-- cycle(system1000): 1, outputVerifier
-- expected value: 99, not equal to actual value: 1
-- ,False,False,False,False,False
-- cycle(system1000): 6, outputVerifier
-- expected value: 7, not equal to actual value: 6
-- ,False
-- cycle(system1000): 7, outputVerifier
-- expected value: 8, not equal to actual value: 7
-- ,False
-- cycle(system1000): 8, outputVerifier
-- expected value: 9, not equal to actual value: 8
-- ,False
-- cycle(system1000): 9, outputVerifier
-- expected value: 10, not equal to actual value: 9
-- ,False,True,True]
outputVerifier :: (KnownNat l, Eq a, Show a, ?res :: Reset rst domain,
                   ?clk :: Clock clk domain)
               => Vec l a     -- ^ Samples to compare with
               -> Signal domain a    -- ^ Signal to verify
               -> Signal domain Bool -- ^ Indicator that all samples are verified
outputVerifier = outputVerifier# ?res ?clk

{-# NOINLINE assert# #-}
-- | Compares the first two 'Signal''s for equality and logs a warning when they
-- are not equal. The second 'Signal'' is considered the expected value. This
-- function simply returns the third 'Signal'' unaltered as its result. This
-- function is used by 'outputVerifier''.
--
--
-- __NB__: This function /can/ be used in synthesizable designs.
assert# :: (Eq a,Show a)
        => Clock clk domain
        -> String          -- ^ Additional message
        -> Signal domain a -- ^ Checked value
        -> Signal domain a -- ^ Expected value
        -> Signal domain b -- ^ Return value
        -> Signal domain b
assert# clk msg checked expected returned =
  (\c e cnt r ->
      if c == e then r
                else trace (concat [ "\ncycle(" ++ show clk ++ "): "
                                   , show cnt
                                   , ", "
                                   , msg
                                   , "\nexpected value: "
                                   , show e
                                   , ", not equal to actual value: "
                                   , show c
                                   ]) r)
  <$> checked <*> expected <*> fromList [(0::Integer)..] <*> returned

{-# INLINABLE stimuliGenerator# #-}
-- | To be used as one of the functions to create the \"magical\" 'testInput'
-- value, which the CλaSH compiler looks for to create the stimulus generator
-- for the generated VHDL testbench.
--
-- Example:
--
-- @
-- type ClkA = 'CLaSH.Signal.Explicit.Clk' \"A\" 100
--
-- clkA :: 'SClock' ClkA
-- clkA = 'CLaSH.Signal.Explicit.sclock'
--
-- testInput' :: 'Signal'' clkA Int
-- testInput' = 'stimuliGenerator'' clkA $('CLaSH.Sized.Vector.v' [(1::Int),3..21])
-- @
--
-- >>> sampleN# 13 testInput#
-- [1,3,5,7,9,11,13,15,17,19,21,21,21]
stimuliGenerator# :: forall domain res clk l a . KnownNat l
                  => Reset res domain
                  -> Clock clk domain -- ^ Clock to which to synchronize the
                                      -- output signal
                  -> Vec l a          -- ^ Samples to generate
                  -> Signal domain a  -- ^ Signal of given samples
stimuliGenerator# res clk samples =
    let (r,o) = unbundle (genT <$> register# res clk 0 r)
    in  o
  where
    genT :: Index l -> (Index l,a)
    genT s = (s',samples !! s)
      where
        maxI = toEnum (maxIndex samples)

        s' = if s < maxI
                then s + 1
                else s

{-# INLINABLE outputVerifier# #-}
-- | To be used as one of the functions to generate the \"magical\" 'expectedOutput'
-- function, which the CλaSH compiler looks for to create the signal verifier
-- for the generated VHDL testbench.
--
-- Example:
--
-- @
-- type ClkA = 'CLaSH.Signal.Explicit.Clk' \"A\" 100
--
-- clkA :: 'SClock' ClkA
-- clkA = 'CLaSH.Signal.Explicit.sclock'
--
-- expectedOutput' :: 'Signal'' ClkA Int -> 'Signal'' ClkA Bool
-- expectedOutput' = 'outputVerifier'' clkA $('CLaSH.Sized.Vector.v' ([70,99,2,3,4,5,7,8,9,10]::[Int]))
-- @
--
-- >>> import qualified Data.List as List
-- >>> sampleN# 12 (expectedOutput# (fromList ([0..10] List.++ [10,10,10])))
-- <BLANKLINE>
-- cycle(A100): 0, outputVerifier
-- expected value: 70, not equal to actual value: 0
-- [False
-- cycle(A100): 1, outputVerifier
-- expected value: 99, not equal to actual value: 1
-- ,False,False,False,False,False
-- cycle(A100): 6, outputVerifier
-- expected value: 7, not equal to actual value: 6
-- ,False
-- cycle(A100): 7, outputVerifier
-- expected value: 8, not equal to actual value: 7
-- ,False
-- cycle(A100): 8, outputVerifier
-- expected value: 9, not equal to actual value: 8
-- ,False
-- cycle(A100): 9, outputVerifier
-- expected value: 10, not equal to actual value: 9
-- ,False,True,True]
outputVerifier# :: forall domain res clk l a . (KnownNat l, Eq a, Show a)
                => Reset res domain
                -> Clock clk domain -- ^ Clock to which the input signal is
                                    -- synchronized to
                -> Vec l a          -- ^ Samples to compare with
                -> Signal domain a    -- ^ Signal to verify
                -> Signal domain Bool -- ^ Indicator that all samples are verified
outputVerifier# res clk samples i =
    let (s,o) = unbundle (genT <$> register# res clk 0 s)
        (e,f) = unbundle o
    in  assert# clk "outputVerifier" i e (register# res clk False f)
  where
    genT :: Index l -> (Index l,(a,Bool))
    genT s = (s',(samples !! s,finished))
      where
        maxI = toEnum (maxIndex samples)

        s' = if s < maxI
                then s + 1
                else s

        finished = s == maxI
