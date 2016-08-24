{-|
Copyright  :  (C) 2013-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MagicHash             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}

{-# LANGUAGE Unsafe #-}

-- See: https://github.com/clash-lang/clash-compiler/commit/721fcfa9198925661cd836668705f817bddaae3c
-- as to why we need this.
{-# OPTIONS_GHC -fno-cpr-anal #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module CLaSH.Signal.Internal
  ( -- * Datatypes
    Domain (..)
  , Signal (..)
    -- * Clocks and resets
  , ClockKind (..)
  , Clock (..,Clock)
  , clockGate#
  , ResetKind (..)
  , Reset (..)
  , unsafeFromAsyncReset#
  , unsafeToAsyncReset#
  , fromSyncReset#
  , toSyncReset#
    -- * Basic circuits
  , register#
  , delay#
  , regEn#
  , mux
  , signal
    -- * Boolean connectives
  , (.&&.), (.||.), not1
    -- * Simulation functions (not synthesisable)
  , simulate#
    -- ** lazy version
  , simulate_lazy#
    -- * List \<-\> Signal conversion (not synthesisable)
  , sample#
  , sampleN#
  , fromList
    -- ** lazy versions
  , sample_lazy#
  , sampleN_lazy#
  , fromList_lazy
    -- * QuickCheck combinators
  , testFor#
    -- * Type classes
    -- ** 'Eq'-like
  , (.==.), (./=.)
    -- ** 'Ord'-like
  , compare1, (.<.), (.<=.), (.>=.), (.>.)
    -- ** 'Functor'
  , mapSignal#
    -- ** 'Applicative'
  , signal#
  , appSignal#
    -- ** 'Foldable'
  , foldr#
    -- ** 'Traversable'
  , traverse#
    -- ** 'Enum'-like
  , fromEnum1
    -- ** 'Rational'-like
  , toRational1
    -- ** 'Integral'-like
  , toInteger1
    -- ** 'Bits'-like
  , testBit1
  , popCount1
  , shift1
  , rotate1
  , setBit1
  , clearBit1
  , shiftL1
  , unsafeShiftL1
  , shiftR1
  , unsafeShiftR1
  , rotateL1
  , rotateR1
  -- * EXTREMELY EXPERIMENTAL
  , joinSignal#
  )
where

import Control.Applicative        (liftA2, liftA3)
import Control.DeepSeq            (NFData, force)
import Control.Exception          (SomeException, catch, evaluate, throw)
import Data.Bits                  (Bits (..), FiniteBits (..))
import Data.Default               (Default (..))
import GHC.Stack                  (HasCallStack, withFrozenCallStack)
import GHC.TypeLits               (KnownNat, KnownSymbol, Nat, Symbol, natVal)
import Language.Haskell.TH.Syntax (Lift (..))
import System.IO.Unsafe           (unsafeDupablePerformIO)
import Test.QuickCheck            (Arbitrary (..), CoArbitrary(..), Property,
                                   property)

import CLaSH.Class.Num            (ExtendingNum (..), SaturatingNum (..))
import CLaSH.Promoted.Nat         (SNat (..))
import CLaSH.Promoted.Symbol      (SSymbol (..))
import CLaSH.XException           (errorX)

{- $setup
>>> :set -XDataKinds -XMagicHash -XTypeApplications
>>> import qualified Data.List as L
>>> type DomA = 'Domain "A" 100
>>> let clkA = Clock @DomA (signal True)
>>> let rstA = unsafeToAsyncReset# @DomA (fromList (False : L.repeat True))
>>> let oscillate res clk = let s = register# res clk False (CLaSH.Signal.not1 s) in s
>>> let count res clk = let s = regEn# res clk 0 (oscillate res clk) (s + 1) in s
-}

-- | A domain with a name ('Symbol') and a clock period ('Nat')
data Domain = Domain { domainName :: Symbol, clockPeriod :: Nat }

infixr 5 :-
-- | A synchronized signal with samples of type @a@, explicitly synchronized to
-- a @domain@
--
-- __NB__: The constructor, @(':-')@, is __not__ synthesisable.
data Signal (domain :: Domain) a = a :- Signal domain a

-- | Distinction between gated and ungated clock signals
data ClockKind = Original -- ^ A clock signal coming straight from the clock source
               | Derived  -- ^ A clock signal that has been gated


-- | A clock signal belonging to a @domain@
data Clock (clockKind :: ClockKind) (domain :: Domain) where
  Clock# :: SSymbol name
         -> SNat period
         -> Signal ('Domain name period) Bool
         -> Clock clockKind ('Domain name period)

instance Show (Clock clk domain) where
  show (Clock# nm rt@SNat _) = show nm ++ show (natVal rt)

-- | We can only create 'Original' clock signals
pattern Clock :: forall domain name period .
                 (KnownSymbol name, KnownNat period, domain ~ 'Domain name period) => ()
              => Signal domain Bool
              -> Clock 'Original domain
pattern Clock en <- Clock# _nm _rt en
  where
    Clock en = Clock# SSymbol SNat en

-- | Clock gating primitive
clockGate# :: Clock clk domain -> Signal domain Bool -> Clock 'Derived domain
clockGate# (Clock# nm rt en) en' = (Clock# nm rt ((&&) <$> en <*> en'))
{-# NOINLINE clockGate# #-}

-- | The \"kind\" of reset
data ResetKind = Synchronous | Asynchronous

-- | A reset signal belonging to a @domain@
data Reset (resetKind :: ResetKind) (domain :: Domain) where
  Sync  :: Signal domain Bool -> Reset 'Synchronous  domain
  Async :: Signal domain Bool -> Reset 'Asynchronous domain

-- | 'unsafeFromAsyncReset#' is HIGHLY unsafe as it can introduce:
--
-- * meta-stability
-- * combinational loops
unsafeFromAsyncReset# :: Reset 'Asynchronous domain -> Signal domain Bool
unsafeFromAsyncReset# (Async r) = r
{-# NOINLINE unsafeFromAsyncReset# #-}

-- | 'unsafeToAsyncReset#' is HIGHLY unsafe as it can introduce:
--
-- * meta-stability
-- * combinational loop
unsafeToAsyncReset# :: Signal domain Bool -> Reset 'Asynchronous domain
unsafeToAsyncReset# r = Async r
{-# NOINLINE unsafeToAsyncReset# #-}

-- It is safe to treat Synchronous resets as Bool signals
fromSyncReset# :: Reset 'Synchronous domain -> Signal domain Bool
fromSyncReset# (Sync r) = r
{-# NOINLINE fromSyncReset# #-}

-- It is safe to treat Bool signals as Synchronous resets
toSyncReset# :: Signal domain Bool -> Reset 'Synchronous domain
toSyncReset# r = Sync r
{-# NOINLINE toSyncReset# #-}

instance Lift a => Lift (Signal domain a) where
  lift ~(x :- _) = [| signal# x |]

instance Default a => Default (Signal domain a) where
  def = signal# def

instance Functor (Signal domain) where
  fmap = mapSignal#

{-# NOINLINE mapSignal# #-}
mapSignal# :: (a -> b) -> Signal domain a -> Signal domain b
mapSignal# f (a :- as) = f a :- mapSignal# f as

instance Applicative (Signal domain) where
  pure  = signal#
  (<*>) = appSignal#

{-# NOINLINE signal# #-}
signal# :: a -> Signal domain a
signal# a = let s = a :- s in s

{-# NOINLINE appSignal# #-}
appSignal# :: Signal domain (a -> b) -> Signal domain a -> Signal domain b
appSignal# (f :- fs) xs@(~(a :- as)) = f a :- (xs `seq` appSignal# fs as) -- See [NOTE: Lazy ap]

{- NOTE: Lazy ap
Signals ap, i.e (Applicative.<*>), must be lazy in it's second argument:

> appSignal :: Signal domain (a -> b) -> Signal domain a -> Signal domain b
> appSignal (f :- fs) ~(a :- as) = f a :- appSignal fs as

because some feedback loops, such as the loop described in 'system' in the
example at http://hackage.haskell.org/package/clash-prelude-0.10.10/docs/CLaSH-Prelude-BlockRam.html,
will lead to "Exception <<loop>>".

However, this "naive" lazy version is _too_ lazy and induces spaceleaks.
The current version:

> appSignal# :: Signal domain (a -> b) -> Signal domain a -> Signal domain b
> appSignal# (f :- fs) xs@(~(a :- as)) = f a :- (xs `seq` appSignal# fs as)

Is lazy enough to handle the earlier mentioned feedback loops, but doesn't leak
(as much) memory like the "naive" lazy version, because the Signal constructor
of the second argument is evaluated as soon as the tail of the result is evaluated.
-}


{-# NOINLINE joinSignal# #-}
-- | __WARNING: EXTREMELY EXPERIMENTAL__
--
-- The circuit semantics of this operation are unclear and/or non-existent.
-- There is a good reason there is no 'Monad' instance for 'Signal'.
--
-- Is currently treated as 'id' by the CLaSH compiler.
joinSignal# :: Signal domain (Signal domain a) -> Signal domain a
joinSignal# ~(xs :- xss) = head# xs :- joinSignal# (mapSignal# tail# xss)
  where
    head# (x' :- _ )  = x'
    tail# (_  :- xs') = xs'

instance Num a => Num (Signal domain a) where
  (+)         = liftA2 (+)
  (-)         = liftA2 (-)
  (*)         = liftA2 (*)
  negate      = fmap negate
  abs         = fmap abs
  signum      = fmap signum
  fromInteger = signal# . fromInteger

-- | __NB__: Not synthesisable
--
-- __NB__: In \"@'foldr' f z s@\":
--
-- * The function @f@ should be /lazy/ in its second argument.
-- * The @z@ element will never be used.
instance Foldable (Signal domain) where
  foldr = foldr#

{-# NOINLINE foldr# #-}
-- | __NB__: Not synthesisable
--
-- __NB__: In \"@'foldr#' f z s@\":
--
-- * The function @f@ should be /lazy/ in its second argument.
-- * The @z@ element will never be used.
foldr# :: (a -> b -> b) -> b -> Signal domain a -> b
foldr# f z (a :- s) = a `f` (foldr# f z s)

instance Traversable (Signal domain) where
  traverse = traverse#

{-# NOINLINE traverse# #-}
traverse# :: Applicative f => (a -> f b) -> Signal domain a -> f (Signal domain b)
traverse# f (a :- s) = (:-) <$> f a <*> traverse# f s

infixr 2 .||.
-- | The above type is a generalisation for:
--
-- @
-- __(.||.)__ :: 'CLaSH.Signal.Signal 'Bool' -> 'CLaSH.Signal.Signal 'Bool' -> 'CLaSH.Signal.Signal 'Bool'
-- @
--
-- It is a version of ('||') that returns a 'CLaSH.Signal.Signal of 'Bool'
(.||.) :: Applicative f => f Bool -> f Bool -> f Bool
(.||.) = liftA2 (||)

infixr 3 .&&.
-- | The above type is a generalisation for:
--
-- @
-- __(.&&.)__ :: 'CLaSH.Signal.Signal 'Bool' -> 'CLaSH.Signal.Signal 'Bool' -> 'CLaSH.Signal.Signal 'Bool'
-- @
--
-- It is a version of ('&&') that returns a 'CLaSH.Signal.Signal of 'Bool'
(.&&.) :: Applicative f => f Bool -> f Bool -> f Bool
(.&&.) = liftA2 (&&)

-- | The above type is a generalisation for:
--
-- @
-- __not1__ :: 'CLaSH.Signal.Signal 'Bool' -> 'CLaSH.Signal.Signal 'Bool'
-- @
--
-- It is a version of 'not' that operates on 'CLaSH.Signal.Signals of 'Bool'
not1 :: Functor f => f Bool -> f Bool
not1 = fmap not

-- | \"@'register#' i s@\" delays the values in 'Signal @s@ for one cycle,
-- and sets the value at time 0 to @i@
--
-- @
-- type ClkA = 'Clk' \"A\" 100
--
-- clkA :: 'SClock' ClkA
-- clkA = 'sclock'
-- @
--
-- >>> sampleN# 3 (register# rstA clkA 8 (fromList [1,2,3,4]))
-- [8,1,2]
register# :: HasCallStack
          => Reset reset domain -> Clock clk domain
          -> a
          -> Signal domain a
          -> Signal domain a
register# (Sync r) (Clock# _ _ en) i d =
  let q  = reg q'
      q' = mux en d' q
      d' = mux r d (pure i) -- negated reset
  in  q
  where reg s = withFrozenCallStack (errorX msg) :- s
        msg   = "register: initial value undefined"

register# (Async r) (Clock# _ _ en) i d =
  let q  = reg q'
      q' = mux en d q
  in  mux r q (pure i) -- negated reset
  where reg s = withFrozenCallStack (errorX msg) :- s
        msg   = "register: initial value undefined"
{-# NOINLINE register# #-}

delay# :: HasCallStack
       => Clock clk domain
       -> Signal domain a
       -> Signal domain a
delay# (Clock# _ _ en) d =
  let q  = reg q'
      q' = mux en d q
  in  q
  where reg s = withFrozenCallStack (errorX msg) :- s
        msg   = "delay: initial value undefined"
{-# NOINLINE delay# #-}

-- | Version of 'register#' that only updates its content when its third
-- argument is asserted. So given:
--
-- @
-- type ClkA = 'Clk' \"A\" 100
-- clkA :: 'SClock' ClkA
-- clkA = 'sclock'
--
-- oscillate = 'register'' clkA False ('CLaSH.Signal.not1' oscillate)
-- count     = 'regEn'' clkA 0 oscillate (count + 1)
-- @
--
-- We get:
--
-- >>> sampleN# 8 (oscillate rstA clkA)
-- [False,True,False,True,False,True,False,True]
-- >>> sampleN# 8 (count rstA clkA)
-- [0,0,1,1,2,2,3,3]
regEn# :: HasCallStack
       => Reset reset domain -> Clock clk domain
       -> a
       -> Signal domain Bool
       -> Signal domain a
       -> Signal domain a
regEn# r clk i en d
  = let q  = withFrozenCallStack (register# r clk i q')
        q' = mux en d q
    in  q
{-# NOINLINE regEn# #-}

{-# INLINE mux #-}
-- | The above type is a generalisation for:
--
-- @
-- __mux__ :: 'CLaSH.Signal.Signal 'Bool' -> 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal a
-- @
--
-- A multiplexer. Given "@'mux' b t f@", output @t@ when @b@ is 'True', and @f@
-- when @b@ is 'False'.
mux :: Applicative f => f Bool -> f a -> f a -> f a
mux = liftA3 (\b t f -> if b then t else f)

{-# INLINE signal #-}
-- | The above type is a generalisation for:
--
-- @
-- __signal__ :: a -> 'CLaSH.Signal.Signal a
-- @
--
-- Create a constant 'CLaSH.Signal.Signal from a combinational value
--
-- >>> sampleN# 5 (signal 4 :: Signal dom Int)
-- [4,4,4,4,4]
signal :: Applicative f => a -> f a
signal = pure

instance Bounded a => Bounded (Signal domain a) where
  minBound = signal# minBound
  maxBound = signal# maxBound

instance ExtendingNum a b => ExtendingNum (Signal domain a) (Signal domain b) where
  type AResult (Signal domain a) (Signal domain b) = Signal domain (AResult a b)
  plus  = liftA2 plus
  minus = liftA2 minus
  type MResult (Signal domain a) (Signal domain b) = Signal domain (MResult a b)
  times = liftA2 times

instance SaturatingNum a => SaturatingNum (Signal domain a) where
  satPlus s = liftA2 (satPlus s)
  satMin  s = liftA2 (satMin s)
  satMult s = liftA2 (satMult s)

-- | __WARNING__: ('==') and ('/=') are undefined, use ('.==.') and ('./=.')
-- instead
instance Eq (Signal domain a) where
  (==) = error "(==)' undefined for 'Signal', use '(.==.)' instead"
  (/=) = error "(/=)' undefined for 'Signal', use '(./=.)' instead"

infix 4 .==.
-- | The above type is a generalisation for:
--
-- @
-- __(.==.)__ :: 'Eq' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Bool'
-- @
--
-- It is a version of ('==') that returns a 'CLaSH.Signal.Signal of 'Bool'
(.==.) :: (Eq a, Applicative f) => f a -> f a -> f Bool
(.==.) = liftA2 (==)

infix 4 ./=.
-- | The above type is a generalisation for:
--
-- @
-- __(./=.)__ :: 'Eq' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Bool'
-- @
--
-- It is a version of ('/=') that returns a 'CLaSH.Signal.Signal of 'Bool'
(./=.) :: (Eq a, Applicative f) => f a -> f a -> f Bool
(./=.) = liftA2 (/=)

-- | __WARNING__: 'compare', ('<'), ('>='), ('>'), and ('<=') are
-- undefined, use 'compare1', ('.<.'), ('.>=.'), ('.>.'), and ('.<=.') instead
instance Ord a => Ord (Signal domain a) where
  compare = error "'compare' undefined for 'Signal', use 'compare1' instead"
  (<)     = error "'(<)' undefined for 'Signal', use '(.<.)' instead"
  (>=)    = error "'(>=)' undefined for 'Signal', use '(.>=.)' instead"
  (>)     = error "'(>)' undefined for 'Signal', use '(.>.)' instead"
  (<=)    = error "'(<=)' undefined for 'Signal', use '(.<=.)' instead"
  max     = liftA2 max
  min     = liftA2 min

-- | The above type is a generalisation for:
--
-- @
-- __compare1__ :: 'Ord' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Ordering'
-- @
--
-- It is a version of 'compare' that returns a 'CLaSH.Signal.Signal of 'Ordering'
compare1 :: (Ord a, Applicative f) => f a -> f a -> f Ordering
compare1 = liftA2 compare

infix 4 .<.
-- | The above type is a generalisation for:
--
-- @
-- __(.<.)__ :: 'Ord' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Bool'
-- @
--
-- It is a version of ('<') that returns a 'CLaSH.Signal.Signal of 'Bool'
(.<.) :: (Ord a, Applicative f) => f a -> f a -> f Bool
(.<.) = liftA2 (<)

infix 4 .<=.
-- | The above type is a generalisation for:
--
-- @
-- __(.<=.)__ :: 'Ord' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Bool'
-- @
--
-- It is a version of ('<=') that returns a 'CLaSH.Signal.Signal of 'Bool'
(.<=.) :: (Ord a, Applicative f) => f a -> f a -> f Bool
(.<=.) = liftA2 (<=)

infix 4 .>.
-- | The above type is a generalisation for:
--
-- @
-- __(.>.)__ :: 'Ord' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Bool'
-- @
--
-- It is a version of ('>') that returns a 'CLaSH.Signal.Signal of 'Bool'
(.>.) :: (Ord a, Applicative f) => f a -> f a -> f Bool
(.>.) = liftA2 (>)

infix 4 .>=.
-- | The above type is a generalisation for:
--
-- @
-- __(.>=.)__ :: 'Ord' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Bool'
-- @
--
--  It is a version of ('>=') that returns a 'CLaSH.Signal.Signal of 'Bool'
(.>=.) :: (Ord a, Applicative f) => f a -> f a -> f Bool
(.>=.) = liftA2 (>=)

-- | __WARNING__: 'fromEnum' is undefined, use 'fromEnum1' instead
instance Enum a => Enum (Signal domain a) where
  succ           = fmap succ
  pred           = fmap pred
  toEnum         = signal# . toEnum
  fromEnum       = error "'fromEnum' undefined for 'Signal', use 'fromEnum1'"
  enumFrom       = sequenceA . fmap enumFrom
  enumFromThen   = (sequenceA .) . liftA2 enumFromThen
  enumFromTo     = (sequenceA .) . liftA2 enumFromTo
  enumFromThenTo = ((sequenceA .) .) . liftA3 enumFromThenTo

-- | The above type is a generalisation for:
--
-- @
-- __fromEnum1__ :: 'Enum' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Int'
-- @
--
-- It is a version of 'fromEnum' that returns a CLaSH.Signal.Signal of 'Int'
fromEnum1 :: (Enum a, Functor f) => f a -> f Int
fromEnum1 = fmap fromEnum

-- | __WARNING__: 'toRational' is undefined, use 'toRational1' instead
instance (Num a, Ord a) => Real (Signal domain a) where
  toRational = error "'toRational' undefined for 'Signal', use 'toRational1'"

-- | The above type is a generalisation for:
--
-- @
-- __toRational1__ :: 'Real' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Rational'
-- @
--
-- It is a version of 'toRational' that returns a 'CLaSH.Signal.Signal of 'Rational'
toRational1 :: (Real a, Functor f) => f a -> f Rational
toRational1 = fmap toRational

-- | __WARNING__: 'toInteger' is undefined, use 'toInteger1' instead
instance Integral a => Integral (Signal domain a) where
  quot        = liftA2 quot
  rem         = liftA2 rem
  div         = liftA2 div
  mod         = liftA2 mod
  quotRem a b = (quot a b, rem a b)
  divMod a b  = (div a b, mod a b)
  toInteger   = error "'toInteger' undefined for 'Signal', use 'toInteger1'"

-- | The above type is a generalisation for:
--
-- @
-- __toInteger1__ :: 'Integral' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Integer'
-- @
--
-- It is a version of 'toRational' that returns a 'CLaSH.Signal.Signal of 'Integer'
toInteger1 :: (Integral a, Functor f) => f a -> f Integer
toInteger1 = fmap toInteger

-- | __WARNING__: 'testBit' and 'popCount' are undefined, use 'testBit1' and
-- 'popCount1' instead
instance Bits a => Bits (Signal domain a) where
  (.&.)            = liftA2 (.&.)
  (.|.)            = liftA2 (.|.)
  xor              = liftA2 xor
  complement       = fmap complement
  shift a i        = fmap (`shift` i) a
  rotate a i       = fmap (`rotate` i) a
  zeroBits         = signal# zeroBits
  bit              = signal# . bit
  setBit a i       = fmap (`setBit` i) a
  clearBit a i     = fmap (`clearBit` i) a
  testBit          = error "'testBit' undefined for 'Signal', use 'testbit1'"
  bitSizeMaybe _   = bitSizeMaybe (undefined :: a)
  bitSize _        = maybe 0 id (bitSizeMaybe (undefined :: a))
  isSigned _       = isSigned (undefined :: a)
  shiftL a i       = fmap (`shiftL` i) a
  unsafeShiftL a i = fmap (`unsafeShiftL` i) a
  shiftR a i       = fmap (`shiftR` i) a
  unsafeShiftR a i = fmap (`unsafeShiftR` i) a
  rotateL a i      = fmap (`rotateL` i) a
  rotateR a i      = fmap (`rotateR` i) a
  popCount         = error "'popCount' undefined for 'Signal', use 'popCount1'"

instance FiniteBits a => FiniteBits (Signal domain a) where
  finiteBitSize _ = finiteBitSize (undefined :: a)

-- | The above type is a generalisation for:
--
-- @
-- __testBit1__ :: 'Bits' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Int' -> 'CLaSH.Signal.Signal 'Bool'
-- @
--
-- It is a version of 'testBit' that has a 'CLaSH.Signal.Signal of 'Int' as indexing
-- argument, and a result of 'CLaSH.Signal.Signal of 'Bool'
testBit1 :: (Bits a, Applicative f) => f a -> f Int -> f Bool
testBit1 = liftA2 testBit

-- | The above type is a generalisation for:
--
-- @
-- __popCount1__ :: 'Bits' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Int'
-- @
--
--  It is a version of 'popCount' that returns a 'CLaSH.Signal.Signal of 'Int'
popCount1 :: (Bits a, Functor f) => f a -> f Int
popCount1 = fmap popCount

-- | The above type is a generalisation for:
--
-- @
-- __shift1__ :: 'Bits' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Int' -> 'CLaSH.Signal.Signal 'a'
-- @
--
-- It is a version of 'shift' that has a 'CLaSH.Signal.Signal of 'Int' as indexing argument
shift1 :: (Bits a, Applicative f) => f a -> f Int -> f a
shift1 = liftA2 shift

-- | The above type is a generalisation for:
--
-- @
-- __rotate1__ :: 'Bits' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Int' -> 'CLaSH.Signal.Signal 'a'
-- @
--
-- It is a version of 'rotate' that has a 'CLaSH.Signal.Signal of 'Int' as indexing argument
rotate1 :: (Bits a, Applicative f) => f a -> f Int -> f a
rotate1 = liftA2 rotate

-- | The above type is a generalisation for:
--
-- @
-- __setBit1__ :: 'Bits' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Int' -> 'CLaSH.Signal.Signal 'a'
-- @
--
-- It is a version of 'setBit' that has a 'CLaSH.Signal.Signal of 'Int' as indexing argument
setBit1 :: (Bits a, Applicative f) => f a -> f Int -> f a
setBit1 = liftA2 setBit

-- | The above type is a generalisation for:
--
-- @
-- __clearBit1__ :: 'Bits' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Int' -> 'CLaSH.Signal.Signal 'a'
-- @
--
-- It is a version of 'clearBit' that has a 'CLaSH.Signal.Signal of 'Int' as indexing argument
clearBit1 :: (Bits a, Applicative f) => f a -> f Int -> f a
clearBit1 = liftA2 clearBit

-- | The above type is a generalisation for:
--
-- @
-- __shiftL1__ :: 'Bits' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Int' -> 'CLaSH.Signal.Signal 'a'
-- @
--
-- It is a version of 'shiftL' that has a 'CLaSH.Signal.Signal of 'Int' as indexing argument
shiftL1 :: (Bits a, Applicative f) => f a -> f Int -> f a
shiftL1 = liftA2 shiftL

-- | The above type is a generalisation for:
--
-- @
-- __unsafeShiftL1__ :: 'Bits' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Int' -> 'CLaSH.Signal.Signal 'a'
-- @
--
-- It is a version of 'unsafeShiftL' that has a 'CLaSH.Signal.Signal of 'Int' as indexing argument
unsafeShiftL1 :: (Bits a, Applicative f) => f a -> f Int -> f a
unsafeShiftL1 = liftA2 unsafeShiftL

-- | The above type is a generalisation for:
--
-- @
-- __shiftR1__ :: 'Bits' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Int' -> 'CLaSH.Signal.Signal 'a'
-- @
--
-- It is a version of 'shiftR' that has a 'CLaSH.Signal.Signal of 'Int' as indexing argument
shiftR1 :: (Bits a, Applicative f) => f a -> f Int -> f a
shiftR1 = liftA2 shiftR

-- | The above type is a generalisation for:
--
-- @
-- __unsafeShiftR1__ :: 'Bits' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Int' -> 'CLaSH.Signal.Signal 'a'
-- @
--
-- It is a version of 'unsafeShiftR' that has a 'CLaSH.Signal.Signal of 'Int' as indexing argument
unsafeShiftR1 :: (Bits a, Applicative f) => f a -> f Int -> f a
unsafeShiftR1 = liftA2 unsafeShiftR

-- | The above type is a generalisation for:
--
-- @
-- __rotateL1__ :: 'Bits' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Int' -> 'CLaSH.Signal.Signal 'a'
-- @
--
-- It is a version of 'rotateL' that has a 'CLaSH.Signal.Signal of 'Int' as indexing argument
rotateL1 :: (Bits a, Applicative f) => f a -> f Int -> f a
rotateL1 = liftA2 rotateL

-- | The above type is a generalisation for:
--
-- @
-- __rotateR1__ :: 'Bits' a => 'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal 'Int' -> 'CLaSH.Signal.Signal 'a'
-- @
--
-- It is a version of 'rotateR' that has a 'CLaSH.Signal.Signal of 'Int' as indexing argument
rotateR1 :: (Bits a, Applicative f) => f a -> f Int -> f a
rotateR1 = liftA2 rotateR

instance Fractional a => Fractional (Signal domain a) where
  (/)          = liftA2 (/)
  recip        = fmap recip
  fromRational = signal# . fromRational

instance Arbitrary a => Arbitrary (Signal domain a) where
  arbitrary = liftA2 (:-) arbitrary arbitrary

instance CoArbitrary a => CoArbitrary (Signal domain a) where
  coarbitrary xs gen = do
    n <- arbitrary
    coarbitrary (take (abs n) (sample_lazy# xs)) gen

-- | The above type is a generalisation for:
--
-- @
-- __testFor__ :: 'Int' -> 'CLaSH.Signal.Signal Bool -> 'Property'
-- @
--
-- @testFor n s@ tests the signal @s@ for @n@ cycles.
testFor# :: Foldable f => Int -> f Bool -> Property
testFor# n = property . and . take n . sample#

-- * List \<-\> Signal conversion (not synthesisable)

-- | A 'force' that lazily returns exceptions
forceNoException :: NFData a => a -> IO a
forceNoException x = catch (evaluate (force x)) (\(e :: SomeException) -> return (throw e))

headStrictCons :: NFData a => a -> [a] -> [a]
headStrictCons x xs = unsafeDupablePerformIO ((:) <$> forceNoException x <*> pure xs)

headStrictSignal :: NFData a => a -> Signal domain a -> Signal domain a
headStrictSignal x xs = unsafeDupablePerformIO ((:-) <$> forceNoException x <*> pure xs)

-- | The above type is a generalisation for:
--
-- @
-- __sample__ :: 'CLaSH.Signal.Signal a -> [a]
-- @
--
-- Get an infinite list of samples from a 'CLaSH.Signal.Signal
--
-- The elements in the list correspond to the values of the 'CLaSH.Signal.Signal
-- at consecutive clock cycles
--
-- > sample s == [s0, s1, s2, s3, ...
--
-- __NB__: This function is not synthesisable
sample# :: (Foldable f, NFData a) => f a -> [a]
sample# = foldr headStrictCons []

-- | The above type is a generalisation for:
--
-- @
-- __sampleN__ :: Int -> 'CLaSH.Signal.Signal a -> [a]
-- @
--
-- Get a list of @n@ samples from a 'CLaSH.Signal.Signal
--
-- The elements in the list correspond to the values of the 'CLaSH.Signal.Signal
-- at consecutive clock cycles
--
-- > sampleN 3 s == [s0, s1, s2]
--
-- __NB__: This function is not synthesisable
sampleN# :: (Foldable f, NFData a) => Int -> f a -> [a]
sampleN# n = take n . sample#

-- | Create a 'CLaSH.Signal.Signal from a list
--
-- Every element in the list will correspond to a value of the signal for one
-- clock cycle.
--
-- >>> sampleN# 2 (fromList [1,2,3,4,5])
-- [1,2]
--
-- __NB__: This function is not synthesisable
fromList :: NFData a => [a] -> Signal domain a
fromList = Prelude.foldr headStrictSignal (error "finite list")

-- * Simulation functions (not synthesisable)

-- | Simulate a (@'CLaSH.Signal.Signal a -> 'CLaSH.Signal.Signal b@) function
-- given a list of samples of type @a@
--
-- >>> simulate# (register# rstA clkA 8) [1, 2, 3]
-- [8,1,2,3...
-- ...
--
-- __NB__: This function is not synthesisable
simulate# :: (NFData a, NFData b) => (Signal domain1 a -> Signal domain2 b) -> [a] -> [b]
simulate# f = sample# . f . fromList

-- | The above type is a generalisation for:
--
-- @
-- __sample__ :: 'CLaSH.Signal.Signal' a -> [a]
-- @
--
-- Get an infinite list of samples from a 'CLaSH.Signal.Signal'
--
-- The elements in the list correspond to the values of the 'CLaSH.Signal.Signal'
-- at consecutive clock cycles
--
-- > sample s == [s0, s1, s2, s3, ...
--
-- __NB__: This function is not synthesisable
sample_lazy# :: Foldable f => f a -> [a]
sample_lazy# = foldr (:) []

-- | The above type is a generalisation for:
--
-- @
-- __sampleN__ :: Int -> 'CLaSH.Signal.Signal' a -> [a]
-- @
--
-- Get a list of @n@ samples from a 'CLaSH.Signal.Signal'
--
-- The elements in the list correspond to the values of the 'CLaSH.Signal.Signal'
-- at consecutive clock cycles
--
-- > sampleN 3 s == [s0, s1, s2]
--
-- __NB__: This function is not synthesisable
sampleN_lazy# :: Foldable f => Int -> f a -> [a]
sampleN_lazy# n = take n . sample_lazy#

-- | Create a 'CLaSH.Signal.Signal' from a list
--
-- Every element in the list will correspond to a value of the signal for one
-- clock cycle.
--
-- >>> sampleN# 2 (fromList [1,2,3,4,5])
-- [1,2]
--
-- __NB__: This function is not synthesisable
fromList_lazy :: [a] -> Signal clk a
fromList_lazy = Prelude.foldr (:-) (error "finite list")

-- * Simulation functions (not synthesisable)

-- | Simulate a (@'CLaSH.Signal.Signal' a -> 'CLaSH.Signal.Signal' b@) function
-- given a list of samples of type @a@
--
-- >>> simulate# (register# rstA clkA 8) [1, 2, 3]
-- [8,1,2,3...
-- ...
--
-- __NB__: This function is not synthesisable
simulate_lazy# :: (Signal domain1 a -> Signal domain2 b) -> [a] -> [b]
simulate_lazy# f = sample_lazy# . f . fromList_lazy
