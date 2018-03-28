{-|
Copyright  :  (C) 2013-2016, University of Twente,
                  2016     , Myrtle Software,
                  2017     , Google Inc.
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

CλaSH has synchronous 'Signal's in the form of:

@
'Signal' (domain :: 'Domain') a
@

Where /a/ is the type of the value of the 'Signal', for example /Int/ or /Bool/,
and /domain/ is the /clock-/ (and /reset-/) domain to which the memory elements
manipulating these 'Signal's belong.

The type-parameter, /domain/, is of the kind 'Domain' which has types of the
following shape:

@
data Domain = Dom { domainName :: 'GHC.TypeLits.Symbol', clkPeriod :: 'GHC.TypeLits.Nat' }
@

Where /domainName/ is a type-level string ('GHC.TypeLits.Symbol') representing
the name of the /clock-/ (and /reset-/) domain, and /clkPeriod/ is a type-level
natural number ('GHC.TypeLits.Nat') representing the clock period (in __ps__)
of the clock lines in the /clock-domain/.

* __NB__: \"Bad things\"™  happen when you actually use a clock period of @0@,
so do __not__ do that!
* __NB__: You should be judicious using a clock with period of @1@ as you can
never create a clock that goes any faster!
-}

{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

{-# LANGUAGE Trustworthy #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_HADDOCK show-extensions #-}

module Clash.Signal
  ( -- * Synchronous signals
    Signal
  , Domain (..)
  , System
    -- * Clock
  , Clock
  , ClockKind (..)
    -- * Reset
  , Reset
  , ResetKind (..)
  , unsafeFromAsyncReset
  , unsafeToAsyncReset
  , fromSyncReset
  , unsafeToSyncReset
  , resetSynchronizer
    -- * Hidden clocks and resets
    -- $hiddenclockandreset

    -- ** Hidden clock
  , SomeClock
  , HiddenClock
  , hideClock
  , exposeClock
    -- ** Hidden reset
  , SomeReset
  , HiddenReset
  , hideReset
  , exposeReset
    -- ** Hidden clock and reset
  , HiddenClockReset
  , hideClockReset
  , exposeClockReset
  , SystemClockReset
    -- * Basic circuit functions
  , delay
  , register
  , regMaybe
  , regEn
  , mux
    -- * Simulation and testbench functions
  , clockGen
  , tbClockGen
  , asyncResetGen
  , syncResetGen
  , systemClockGen
  , tbSystemClockGen
  , systemResetGen
    -- * Boolean connectives
  , (.&&.), (.||.)
    -- * Product/Signal isomorphism
  , Bundle(..)
    -- * Simulation functions (not synthesisable)
  , simulate
  , simulateB
    -- ** lazy versions
  , simulate_lazy
  , simulateB_lazy
    -- * List \<-\> Signal conversion (not synthesisable)
  , sample
  , sampleN
  , fromList
    -- ** lazy versions
  , sample_lazy
  , sampleN_lazy
  , fromList_lazy
    -- * QuickCheck combinators
  , testFor
    -- * Type classes
    -- ** 'Eq'-like
  , (.==.), (./=.)
    -- ** 'Ord'-like
  , (.<.), (.<=.), (.>=.), (.>.)
  )
where

import           Control.DeepSeq       (NFData)
import           GHC.Stack             (HasCallStack, withFrozenCallStack)
import           GHC.TypeLits          (KnownNat, KnownSymbol)
import           Data.Bits             (Bits) -- Haddock only
import           Data.Maybe            (isJust, fromJust)
import           Data.Reflection       (Given (..), give)
import           Test.QuickCheck       (Property, property)
import           Unsafe.Coerce         (unsafeCoerce)

import           Clash.Explicit.Signal
  (System, resetSynchronizer, systemClockGen, systemResetGen, tbSystemClockGen)
import qualified Clash.Explicit.Signal as S
import           Clash.Promoted.Nat    (SNat (..))
import           Clash.Promoted.Symbol (SSymbol (..))
import           Clash.Signal.Bundle   (Bundle (..))
import           Clash.Signal.Internal hiding
  (sample, sample_lazy, sampleN, sampleN_lazy, simulate, simulate_lazy, testFor)
import qualified Clash.Signal.Internal as S

{- $setup
>>> :set -XFlexibleContexts -XTypeApplications
>>> import Clash.XException (printX)
>>> import Control.Applicative (liftA2)
>>> let oscillate = register False (not <$> oscillate)
>>> let count = regEn 0 oscillate (count + 1)
>>> :{
sometimes1 = s where
  s = register Nothing (switch <$> s)
  switch Nothing = Just 1
  switch _       = Nothing
:}

>>> :{
countSometimes = s where
  s     = regMaybe 0 (plusM (pure <$> s) sometimes1)
  plusM = liftA2 (liftA2 (+))
:}

-}

-- * Hidden clock and reset arguments

{- $hiddenclockandreset #hiddenclockandreset#
Clocks and resets are by default implicitly routed to their components. You can
see from the type of a component whether it has hidden clock or reset
arguments:

It has a hidden clock when it has a:

@
f :: 'HiddenClock' domain gated => ...
@

Constraint.

Or it has a hidden reset when it has a:

@
g :: 'HiddenReset' domain synchronous => ...
@

Constraint.

Or it has both a hidden clock argument and a hidden reset argument when it
has a:

@
h :: 'HiddenClockReset' domain gated synchronous => ..
@

Constraint.

Given a component with an explicit clock and reset arguments, you can turn them
into hidden arguments using 'hideClock' and 'hideReset'. So given a:

@
f :: Clock domain gated -> Reset domain synchronous -> Signal domain a -> ...
@

You hide the clock and reset arguments by:

@
-- g :: 'HiddenClockReset' domain gated synchronous => Signal domain a -> ...
g = 'hideClockReset' f
@

=== Assigning explicit clock and reset arguments to hidden clocks and resets

Given a component:

@
f :: HiddenClockReset domain gated synchronous
  => Signal domain Int
  -> Signal domain Int
@

which has hidden clock and routed reset arguments, we expose those hidden
arguments so that we can explicitly apply them:

@
-- g :: Clock domain gated -> Reset domain synchronous -> Signal domain Int -> Signal domain Int
g = 'exposeClockReset' f
@

Similarly, there are 'exposeClock' and 'exposeReset' to connect just expose
the hidden clock or the hidden reset argument.

You will need to explicitly apply clocks and resets when you want to use
components such as PPLs and 'resetSynchronizer':

@
topEntity
  :: Clock System Source
  -> Reset System Asynchronous
  -> Signal System Int
  -> Signal System Int
topEntity clk rst =
  let (pllOut,pllStable) = 'Clash.Intel.ClockGen.altpll' (SSymbol \@\"altpll50\") clk rst
      rstSync            = 'resetSynchronizer' pllOut ('unsafeToAsyncReset' pllStable)
  in  'exposeClockReset' f pllOut rstSync
@

-}

-- | A clock that is polymorphic in whether it's gated or not
data SomeClock domain where
  SomeClock :: Clock domain gated -> SomeClock domain

-- | A /constraint/ that indicates the component has a hidden 'Clock'
--
-- <Clash-Signal.html#hiddenclockandreset Click here to read more about hidden clocks and resets>
type HiddenClock domain = Given (SomeClock domain)

-- | A reset that is polymorphic in whether it's synchronous or asynchronous
data SomeReset domain where
  SomeReset :: Reset domain synchronous -> SomeReset domain

-- | A /constraint/ that indicates the component needs a 'Reset'
--
-- <Clash-Signal.html#hiddenclockandreset Click here to read more about hidden clocks and resets>
type HiddenReset domain = Given (SomeReset domain)

-- | A /constraint/ that indicates the component needs a 'Clock' and 'Reset'
--
-- <Clash-Signal.html#hiddenclockandreset Click here to read more about hidden clocks and resets>
type HiddenClockReset domain = (HiddenClock domain, HiddenReset domain)

-- | A /constraint/ that indicates the component needs a 'Clock' and a 'Reset'
-- belonging to the 'System' domain.
--
-- <Clash-Signal.html#hiddenclockandreset Click here to read more about hidden clocks and resets>
type SystemClockReset = HiddenClockReset System

-- | Expose the hidden 'Clock' argument of a component, so it can be applied
-- explicitly
--
-- <Clash-Signal.html#hiddenclockandreset Click here to read more about hidden clocks and resets>
exposeClock
  :: (HiddenClock domain => r)
  -- ^ The component with a hidden clock
  -> (Clock domain gated -> r)
  -- ^ The component with its clock argument exposed
exposeClock = \f clk -> give (SomeClock clk) f
{-# INLINE exposeClock #-}

-- | Hide the 'Clock' argument of a component, so it can be routed implicitly.
hideClock
  :: HiddenClock domain
  => (forall gated . Clock domain gated -> r)
  -- ^ Function whose clock argument you want to hide
  -> r
hideClock = \f -> case given of SomeClock clk -> f clk
{-# INLINE hideClock #-}

-- | Expose the hidden 'Reset' argument of a component, so it can be applied
-- explicitly
--
-- <Clash-Signal.html#hiddenclockandreset Click here to read more about hidden clocks and resets>
exposeReset
  :: (HiddenReset domain => r)
  -- ^ The component with a hidden reset
  -> (Reset domain synchronous -> r)
  -- ^ The component with its reset argument exposed
exposeReset = \f rst -> give (SomeReset rst) f
{-# INLINE exposeReset #-}

-- | Hide the 'Reset' argument of a component, so it can be routed implicitly.
hideReset
  :: HiddenReset domain
  => (forall synchronous . Reset domain synchronous -> r)
  -- ^ Component whose reset argument you want to hide
  -> r
hideReset = \f -> case given of SomeReset rst -> f rst
{-# INLINE hideReset #-}

-- | Expose the hidden 'Clock' and 'Reset' arguments of a component, so they can
-- be applied explicitly
--
-- <Clash-Signal.html#hiddenclockandreset Click here to read more about hidden clocks and resets>
--
-- === __Example__
--
-- @
-- topEntity :: Vec 2 (Vec 3 (Unsigned 8)) -> Vec 6 (Unsigned 8)
-- topEntity = concat
--
-- testBench :: Signal System Bool
-- testBench = done
--   where
--     testInput      = pure ((1 :> 2 :> 3 :> Nil) :> (4 :> 5 :> 6 :> Nil) :> Nil)
--     expectedOutput = outputVerifier ((1:>2:>3:>4:>5:>6:>Nil):>Nil)
--     done           = exposeClockReset (expectedOutput (topEntity <$> testInput)) clk rst
--     clk            = tbSystemClockGen (not <\$\> done)
--     rst            = systemResetGen
-- @
exposeClockReset
  :: (HiddenClockReset domain => r)
  -- ^ The component with hidden clock and reset arguments
  -> (Clock domain gated -> Reset domain synchronous -> r)
  -- ^ The component with its clock and reset arguments exposed
exposeClockReset = \f clk rst -> give (SomeReset rst) ((give (SomeClock clk) f))
{-# INLINE exposeClockReset #-}

-- | Hide the 'Clock' and 'Reset' arguments of a component, so they can be
-- routed implicitly
hideClockReset
  :: HiddenClockReset domain
  => (forall gated synchronous . Clock domain gated -> Reset domain synchronous -> r)
  -- ^ Component whose clock and reset argument you want to hide
  -> r
hideClockReset = \f -> hideReset (hideClock f)
{-# INLINE hideClockReset #-}

-- * Basic circuit functions

-- | 'delay' @s@ delays the values in 'Signal' @s@ for once cycle, the value
-- at time 0 is undefined.
--
-- >>> printX (sampleN 3 (delay (fromList [1,2,3,4])))
-- [X,1,2]
delay
  :: (HiddenClock domain, HasCallStack)
  => Signal domain a
  -- ^ Signal to delay
  -> Signal domain a
delay = \i -> withFrozenCallStack (hideClock delay# i)
{-# INLINE delay #-}

-- | 'register' @i s@ delays the values in 'Signal' @s@ for one cycle, and sets
-- the value at time 0 to @i@
--
-- >>> sampleN 3 (register 8 (fromList [1,2,3,4]))
-- [8,1,2]
register
  :: (HiddenClockReset domain, HasCallStack)
  => a
  -- ^ Reset value
  --
  -- 'register' has an /active-hig/h 'Reset', meaning that 'register' outputs the
  -- reset value when the reset value becomes 'True'
  -> Signal domain a
  -> Signal domain a
register = \i s -> withFrozenCallStack (hideClockReset register# i s)
{-# INLINE register #-}
infixr 3 `register`

-- | Version of 'register' that only updates its content when its second
-- argument is a 'Just' value. So given:
--
-- @
-- sometimes1 = s where
--   s = 'register' Nothing (switch '<$>' s)
--
--   switch Nothing = Just 1
--   switch _       = Nothing
--
-- countSometimes = s where
--   s     = 'regMaybe' 0 (plusM ('pure' '<$>' s) sometimes1)
--   plusM = 'liftA2' (liftA2 (+))
-- @
--
-- We get:
--
-- >>> sampleN 8 sometimes1
-- [Nothing,Just 1,Nothing,Just 1,Nothing,Just 1,Nothing,Just 1]
-- >>> sampleN 8 countSometimes
-- [0,0,1,1,2,2,3,3]
regMaybe
  :: (HiddenClockReset domain, HasCallStack)
  => a
  -- ^ Reset value
  --
  -- 'regMaybe' has an /active-high/ 'Reset', meaning that 'regMaybe' outputs the
  -- reset value when the reset value becomes 'True'
  -> Signal domain (Maybe a)
  -> Signal domain a
regMaybe = \initial iM -> withFrozenCallStack
  (hideClockReset (\clk rst -> register# (clockGate clk (fmap isJust iM)) rst initial (fmap fromJust iM)))
{-# INLINE regMaybe #-}
infixr 3 `regMaybe`

-- | Version of 'register' that only updates its content when its second argument
-- is asserted. So given:
--
-- @
-- oscillate = 'register' False ('not' '<$>' oscillate)
-- count     = 'regEn' 0 oscillate (count + 1)
-- @
--
-- We get:
--
-- >>> sampleN 8 oscillate
-- [False,True,False,True,False,True,False,True]
-- >>> sampleN 8 count
-- [0,0,1,1,2,2,3,3]
regEn
  :: (HiddenClockReset domain, HasCallStack)
  => a
  -- ^ Reset value
  --
  -- 'regEn' has an /active-high/ 'Reset', meaning that 'regEn' outputs the
  -- reset value when the reset value becomes 'True'
  -> Signal domain Bool
  -> Signal domain a
  -> Signal domain a
regEn = \initial en i -> withFrozenCallStack
  (hideClockReset (\clk rst -> register# (clockGate clk en) rst initial i))
{-# INLINE regEn #-}

-- * Signal -> List conversion

-- | Get an infinite list of samples from a 'Clash.Signal.Signal'
--
-- The elements in the list correspond to the values of the 'Signal'
-- at consecutive clock cycles
--
-- > sample s == [s0, s1, s2, s3, ...
--
-- __NB__: This function is not synthesisable
sample
  :: forall domain a
   . NFData a
  => (HiddenClockReset domain => Signal domain a)
  -- ^ 'Signal' we want to sample, whose source potentially has a hidden clock
  -- (and reset)
  -> [a]
sample s =
  let clk = unsafeCoerce @(Clock System 'Source)
                         @(Clock domain 'Source)
                         (Clock @System SSymbol SNat)
      rst = Async (True :- pure False)
  in  S.sample (exposeClockReset s clk rst)

-- | Get a list of /n/ samples from a 'Signal'
--
-- The elements in the list correspond to the values of the 'Signal'
-- at consecutive clock cycles
--
-- > sampleN 3 s == [s0, s1, s2]
--
-- __NB__: This function is not synthesisable
sampleN
  :: forall domain a
   . NFData a
  => Int
  -- ^ The number of samples we want to see
  -> (HiddenClockReset domain => Signal domain a)
  -- ^ 'Signal' we want to sample, whose source potentially has a hidden clock
  -- (and reset)
  -> [a]
sampleN n s =
  let clk = unsafeCoerce @(Clock System 'Source)
                         @(Clock domain 'Source)
                         (Clock @System SSymbol SNat)
      rst = Async (True :- pure False)
  in  S.sampleN n (exposeClockReset s clk rst)

-- | /Lazily/ get an infinite list of samples from a 'Clash.Signal.Signal'
--
-- The elements in the list correspond to the values of the 'Signal'
-- at consecutive clock cycles
--
-- > sample s == [s0, s1, s2, s3, ...
--
-- __NB__: This function is not synthesisable
sample_lazy
  :: forall domain a
   . (HiddenClockReset domain => Signal domain a)
  -- ^ 'Signal' we want to sample, whose source potentially has a hidden clock
  -- (and reset)
  -> [a]
sample_lazy s =
  let clk = unsafeCoerce @(Clock System 'Source)
                         @(Clock domain 'Source)
                         (Clock @System SSymbol SNat)
      rst = Async (True :- pure False)
  in  S.sample_lazy (exposeClockReset s clk rst)


-- | Lazily get a list of /n/ samples from a 'Signal'
--
-- The elements in the list correspond to the values of the 'Signal'
-- at consecutive clock cycles
--
-- > sampleN 3 s == [s0, s1, s2]
--
-- __NB__: This function is not synthesisable
sampleN_lazy
  :: forall domain a
   . Int
  -> (HiddenClockReset domain => Signal domain a)
  -- ^ 'Signal' we want to sample, whose source potentially has a hidden clock
  -- (and reset)
  -> [a]
sampleN_lazy n s =
  let clk = unsafeCoerce @(Clock System 'Source)
                         @(Clock domain 'Source)
                         (Clock @System SSymbol SNat)
      rst = Async (True :- pure False)
  in  S.sampleN_lazy n (exposeClockReset s clk rst)

-- * Simulation functions

-- | Simulate a (@'Signal' a -> 'Signal' b@) function given a list of samples
-- of type /a/
--
-- >>> simulate (register 8) [1, 2, 3]
-- [8,1,2,3...
-- ...
--
-- __NB__: This function is not synthesisable
simulate
  :: forall domain a b
   . (NFData a, NFData b)
  => (HiddenClockReset domain =>
      Signal domain a -> Signal domain b)
  -- ^ 'Signal' we want to sample, whose source potentially has a hidden clock
  -- (and reset)
  -> [a]
  -> [b]
simulate f =
  let clk = unsafeCoerce @(Clock System 'Source)
                         @(Clock domain 'Source)
                         (Clock @System SSymbol SNat)
      rst = Async (True :- pure False)
  in  S.simulate (exposeClockReset f clk rst)

-- | /Lazily/ simulate a (@'Signal' a -> 'Signal' b@) function given a list of
-- samples of type /a/
--
-- >>> simulate (register 8) [1, 2, 3]
-- [8,1,2,3...
-- ...
--
-- __NB__: This function is not synthesisable
simulate_lazy
  :: forall domain a b
   . (HiddenClockReset domain =>
      Signal domain a -> Signal domain b)
  -- ^ Function we want to simulate, whose components potentially have a hidden
  -- clock (and reset)
  -> [a]
  -> [b]
simulate_lazy f =
  let clk = unsafeCoerce @(Clock System 'Source)
                         @(Clock domain 'Source)
                         (Clock @System SSymbol SNat)
      rst = Async (True :- pure False)
  in  S.simulate_lazy (exposeClockReset f clk rst)

-- | Simulate a (@'Unbundled' a -> 'Unbundled' b@) function given a list of
-- samples of type @a@
--
-- >>> simulateB (unbundle . register (8,8) . bundle) [(1,1), (2,2), (3,3)] :: [(Int,Int)]
-- [(8,8),(1,1),(2,2),(3,3)...
-- ...
--
-- __NB__: This function is not synthesisable
simulateB
  :: forall domain a b
   . (Bundle a, Bundle b, NFData a, NFData b)
  => (HiddenClockReset domain =>
      Unbundled domain a -> Unbundled domain b)
  -- ^ Function we want to simulate, whose components potentially have a hidden
  -- clock (and reset)
  -> [a]
  -> [b]
simulateB f =
  let clk = unsafeCoerce @(Clock System 'Source)
                         @(Clock domain 'Source)
                         (Clock @System SSymbol SNat)
      rst = Async (True :- pure False)
  in  S.simulateB (exposeClockReset f clk rst)

-- | /Lazily/ simulate a (@'Unbundled' a -> 'Unbundled' b@) function given a
-- list of samples of type @a@
--
-- >>> simulateB (unbundle . register (8,8) . bundle) [(1,1), (2,2), (3,3)] :: [(Int,Int)]
-- [(8,8),(1,1),(2,2),(3,3)...
-- ...
--
-- __NB__: This function is not synthesisable
simulateB_lazy
  :: forall domain a b
   . (Bundle a, Bundle b)
  => (HiddenClockReset domain =>
      Unbundled domain a -> Unbundled domain b)
  -- ^ Function we want to simulate, whose components potentially have a hidden
  -- clock (and reset)
  -> [a]
  -> [b]
simulateB_lazy f =
  let clk = unsafeCoerce @(Clock System 'Source)
                         @(Clock domain 'Source)
                         (Clock @System SSymbol SNat)
      rst = Async (True :- pure False)
  in  S.simulateB_lazy (exposeClockReset f clk rst)

-- * QuickCheck combinators

-- |  @testFor n s@ tests the signal /s/ for /n/ cycles.
testFor
  :: Int
  -- ^ The number of cycles we want to test for
  -> (HiddenClockReset domain => Signal domain Bool)
  -- ^ 'Signal' we want to evaluate, whose source potentially has a hidden clock
  -- (and reset)
  -> Property
testFor n s = property (and (Clash.Signal.sampleN n s))
