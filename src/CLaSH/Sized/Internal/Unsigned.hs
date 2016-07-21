{-|
Copyright  :  (C) 2013-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE MagicHash                  #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# LANGUAGE Unsafe #-}

{-# OPTIONS_HADDOCK show-extensions #-}

#include "primitive.h"

module CLaSH.Sized.Internal.Unsigned
  ( -- * Datatypes
    Unsigned (..)
    -- * Accessors
    -- ** Length information
  , size#
    -- * Type classes
    -- ** BitConvert
  , pack#
  , unpack#
    -- ** Eq
  , eq#
  , neq#
    -- ** Ord
  , lt#
  , ge#
  , gt#
  , le#
    -- ** Enum (not synthesisable)
  , enumFrom#
  , enumFromThen#
  , enumFromTo#
  , enumFromThenTo#
    -- ** Bounded
  , minBound#
  , maxBound#
    -- ** Num
  , (+#)
  , (-#)
  , (*#)
  , negate#
  , fromInteger#
    -- ** ExtendingNum
  , plus#
  , minus#
  , times#
    -- ** Integral
  , quot#
  , rem#
  , toInteger#
    -- ** Bits
  , and#
  , or#
  , xor#
  , complement#
  , shiftL#
  , shiftR#
  , rotateL#
  , rotateR#
    -- ** Resize
  , resize#
  )
where

import Control.Lens                   (Index, Ixed (..), IxValue)
import Data.Bits                      (Bits (..), FiniteBits (..))
import Data.Data                      (Data)
import Data.Default                   (Default (..))
import Text.Read                      (Read (..), ReadPrec)
import GHC.TypeLits                   (KnownNat, Nat, type (+), natVal)
import Language.Haskell.TH            (TypeQ, appT, conT, litT, numTyLit, sigE)
import Language.Haskell.TH.Syntax     (Lift(..))
import Test.QuickCheck.Arbitrary      (Arbitrary (..), CoArbitrary (..),
                                       arbitraryBoundedIntegral,
                                       coarbitraryIntegral)

import CLaSH.Class.BitPack            (BitPack (..))
import CLaSH.Class.Num                (ExtendingNum (..), SaturatingNum (..),
                                       SaturationMode (..))
import CLaSH.Class.Resize             (Resize (..))
import CLaSH.Prelude.BitIndex         ((!), msb, replaceBit, split)
import CLaSH.Prelude.BitReduction     (reduceOr)
import CLaSH.Promoted.Ord             (Max)
import CLaSH.Sized.Internal.BitVector (BitVector (..), Bit, high, low)
import qualified CLaSH.Sized.Internal.BitVector as BV

-- | Arbitrary-width unsigned integer represented by @n@ bits
--
-- Given @n@ bits, an 'Unsigned' @n@ number has a range of: [0 .. 2^@n@-1]
--
-- __NB__: The 'Num' operators perform @wrap-around@ on overflow. If you want
-- saturation on overflow, check out the 'SaturatingNum' class.
--
-- >>> maxBound :: Unsigned 3
-- 7
-- >>> minBound :: Unsigned 3
-- 0
-- >>> read (show (maxBound :: Unsigned 3)) :: Unsigned 3
-- 7
-- >>> 1 + 2 :: Unsigned 3
-- 3
-- >>> 2 + 6 :: Unsigned 3
-- 0
-- >>> 1 - 3 :: Unsigned 3
-- 6
-- >>> 2 * 3 :: Unsigned 3
-- 6
-- >>> 2 * 4 :: Unsigned 3
-- 0
-- >>> (2 :: Unsigned 3) `times` (4 :: Unsigned 3) :: Unsigned 6
-- 8
-- >>> (2 :: Unsigned 3) `plus` (6 :: Unsigned 3) :: Unsigned 4
-- 8
-- >>> satPlus SatSymmetric 2 6 :: Unsigned 3
-- 7
-- >>> satMin SatSymmetric 2 3 :: Unsigned 3
-- 0
newtype Unsigned (n :: Nat) =
    -- | The constructor, 'U', and the field, 'unsafeToInteger', are not
    -- synthesisable.
    U { unsafeToInteger :: Integer }
  deriving Data

size# :: KnownNat n => Unsigned n -> Int
size# u = fromInteger (natVal u)
{-# PRIMITIVE_I size# #-}

instance KnownNat n => Show (Unsigned n) where
  showsPrec p u = showsPrec p (toInteger# u)
  show u = show (toInteger# u)
  -- We cannot say:
  --
  -- > show (U i) = show i
  --
  -- Because GHC translates that to a cast from Unsigned to Integer,
  -- which the CLaSH compiler can (currently) not handle

-- | None of the 'Read' class' methods are synthesisable.
instance KnownNat n => Read (Unsigned n) where
  readPrec = fromIntegral <$> (readPrec :: ReadPrec Word)

instance BitPack (Unsigned n) where
  type BitSize (Unsigned n) = n
  pack   = pack#
  unpack = unpack#

pack# :: Unsigned n -> BitVector n
pack# (U i) = BV i
{-# PRIMITIVE_I pack# #-}

unpack# :: BitVector n -> Unsigned n
unpack# (BV i) = U i
{-# PRIMITIVE_I unpack# #-}

instance KnownNat n => Eq (Unsigned n) where
  (==) = eq#
  (/=) = neq#

umask :: Integer -> Integer -> Integer
umask sz i = i `mod` (shiftL 1 (fromInteger sz))
{-# INLINE umask #-}

eq# :: KnownNat n => Unsigned n -> Unsigned n -> Bool
eq# u@(U v1) (U v2) = umask (natVal u) v1 == umask (natVal u) v2
{-# PRIMITIVE_I eq# #-}

neq# :: KnownNat n => Unsigned n -> Unsigned n -> Bool
neq# u@(U v1) (U v2) = umask (natVal u) v1 /= umask (natVal u) v2
{-# PRIMITIVE_I neq# #-}

instance KnownNat n => Ord (Unsigned n) where
  (<)  = lt#
  (>=) = ge#
  (>)  = gt#
  (<=) = le#

lt#,ge#,gt#,le# :: KnownNat n => Unsigned n -> Unsigned n -> Bool
lt# u@(U n) (U m) = umask (natVal u) n < umask (natVal u) m
{-# PRIMITIVE_I lt# #-}
ge# u@(U n) (U m) = umask (natVal u) n >= umask (natVal u) m
{-# PRIMITIVE_I ge# #-}
gt# u@(U n) (U m) = umask (natVal u) n > umask (natVal u) m
{-# PRIMITIVE_I gt# #-}
le# u@(U n) (U m) = umask (natVal u) n <= umask (natVal u) m
{-# PRIMITIVE_I le# #-}

-- | The functions: 'enumFrom', 'enumFromThen', 'enumFromTo', and
-- 'enumFromThenTo', are not synthesisable.
instance KnownNat n => Enum (Unsigned n) where
  succ           = (+# fromInteger# 1)
  pred           = (-# fromInteger# 1)
  toEnum         = fromInteger# . toInteger
  fromEnum       = fromEnum . toInteger#
  enumFrom       = enumFrom#
  enumFromThen   = enumFromThen#
  enumFromTo     = enumFromTo#
  enumFromThenTo = enumFromThenTo#

enumFrom#       :: KnownNat n => Unsigned n -> [Unsigned n]
enumFromThen#   :: KnownNat n => Unsigned n -> Unsigned n -> [Unsigned n]
enumFromTo#     :: KnownNat n => Unsigned n -> Unsigned n -> [Unsigned n]
enumFromThenTo# :: KnownNat n => Unsigned n -> Unsigned n -> Unsigned n
                -> [Unsigned n]
enumFrom# x             = map toEnum [fromEnum x ..]
enumFromThen# x y       = map toEnum [fromEnum x, fromEnum y ..]
enumFromTo# x y         = map toEnum [fromEnum x .. fromEnum y]
enumFromThenTo# x1 x2 y = map toEnum [fromEnum x1, fromEnum x2 .. fromEnum y]
{-# PRIMITIVE_I enumFrom# #-}
{-# PRIMITIVE_I enumFromThen# #-}
{-# PRIMITIVE_I enumFromTo# #-}
{-# PRIMITIVE_I enumFromThenTo# #-}

instance KnownNat n => Bounded (Unsigned n) where
  minBound = minBound#
  maxBound = maxBound#

minBound# :: Unsigned n
minBound# = U 0
{-# PRIMITIVE_I minBound# #-}

maxBound# :: KnownNat n => Unsigned n
maxBound# = let res = U (bit (fromInteger (natVal res)) - 1) in res
{-# PRIMITIVE_I maxBound# #-}

instance KnownNat n => Num (Unsigned n) where
  (+)         = (+#)
  (-)         = (-#)
  (*)         = (*#)
  negate      = negate#
  abs         = id
  signum bv   = resize# (unpack# (reduceOr bv))
  fromInteger = fromInteger#

(+#),(-#),(*#) :: Unsigned n -> Unsigned n -> Unsigned n
(+#) (U i) (U j) = U (i + j)
{-# PRIMITIVE_I (+#) #-}

(-#) (U i) (U j) = U (i - j)
{-# PRIMITIVE_I (-#) #-}

(*#) (U i) (U j) = U (i * j)
{-# PRIMITIVE_I (*#) #-}

negate# :: Unsigned n -> Unsigned n
negate# (U i) = U (negate i)
{-# PRIMITIVE_I negate# #-}

fromInteger# :: Integer -> Unsigned n
fromInteger# = U
{-# PRIMITIVE_I fromInteger# #-}

instance ExtendingNum (Unsigned m) (Unsigned n) where
  type AResult (Unsigned m) (Unsigned n) = Unsigned (1 + Max m n)
  plus  = plus#
  minus = minus#
  type MResult (Unsigned m) (Unsigned n) = Unsigned (m + n)
  times = times#

plus#, minus# :: Unsigned m -> Unsigned n -> Unsigned (1 + Max m n)
plus# (U a) (U b) = U (a + b)
{-# PRIMITIVE_I plus# #-}

minus# (U a) (U b) = U (a - b)
{-# PRIMITIVE_I minus# #-}

times# :: Unsigned m -> Unsigned n -> Unsigned (m + n)
times# (U a) (U b) = U (a * b)
{-# PRIMITIVE_I times# #-}

instance KnownNat n => Real (Unsigned n) where
  toRational = toRational . toInteger#

instance KnownNat n => Integral (Unsigned n) where
  quot        = quot#
  rem         = rem#
  div         = quot#
  mod         = rem#
  quotRem n d = (n `quot#` d,n `rem#` d)
  divMod  n d = (n `quot#` d,n `rem#` d)
  toInteger   = toInteger#

quot#,rem# :: Unsigned n -> Unsigned n -> Unsigned n
quot# (U i) (U j) = U (i `quot` j)
{-# PRIMITIVE_I quot# #-}
rem# (U i) (U j) = U (i `rem` j)
{-# PRIMITIVE_I rem# #-}

toInteger# :: KnownNat n => Unsigned n -> Integer
toInteger# u@(U i) = umask (natVal u) i
{-# PRIMITIVE_I toInteger# #-}

instance (KnownNat n, KnownNat (n + 1), KnownNat (n + 2)) => Bits (Unsigned n) where
  (.&.)             = and#
  (.|.)             = or#
  xor               = xor#
  complement        = complement#
  zeroBits          = 0
  bit i             = replaceBit i high 0
  setBit v i        = replaceBit i high v
  clearBit v i      = replaceBit i low  v
  complementBit v i = replaceBit i (BV.complement# (v ! i)) v
  testBit v i       = v ! i == high
  bitSizeMaybe v    = Just (size# v)
  bitSize           = size#
  isSigned _        = False
  shiftL v i        = shiftL# v i
  shiftR v i        = shiftR# v i
  rotateL v i       = rotateL# v i
  rotateR v i       = rotateR# v i
  popCount u        = popCount (pack# u)

and# :: Unsigned n -> Unsigned n -> Unsigned n
and# (U v1) (U v2) = U (v1 .&. v2)
{-# PRIMITIVE_I and# #-}

or# :: Unsigned n -> Unsigned n -> Unsigned n
or# (U v1) (U v2) = U (v1 .|. v2)
{-# PRIMITIVE_I or# #-}

xor# :: Unsigned n -> Unsigned n -> Unsigned n
xor# (U v1) (U v2) = U (v1 `xor` v2)
{-# PRIMITIVE_I xor# #-}

complement# :: Unsigned n -> Unsigned n
complement# (U i) = U (complement i)
{-# PRIMITIVE_I complement# #-}

shiftL#, shiftR#, rotateL#, rotateR# :: KnownNat n => Unsigned n -> Int
                                     -> Unsigned n
shiftL# (U v) i
  | i < 0     = error
              $ "'shiftL undefined for negative number: " ++ show i
  | otherwise = U (shiftL v i)
{-# PRIMITIVE shiftL# #-}

shiftR# u@(U v) i
  | i < 0     = error
              $ "'shiftR undefined for negative number: " ++ show i
  | otherwise = U (shiftR_logical (fromInteger (natVal u)) v i)
{-# PRIMITIVE shiftR# #-}

shiftR_logical :: Int -> Integer -> Int -> Integer
shiftR_logical sz n i = shiftR n i .&. (bit (sz - i) - 1)
{-# INLINE shiftR_logical #-}

rotateL# _ b | b < 0 = error "'shiftL undefined for negative numbers"
rotateL# u@(U n) b   = U (l .|. r)
  where
    l    = shiftL n b'
    r    = shiftR_logical sz n b''

    b'   = b `mod` sz
    b''  = sz - b'
    sz   = fromInteger (natVal u)
{-# PRIMITIVE rotateL# #-}

rotateR# _ b | b < 0 = error "'shiftR undefined for negative numbers"
rotateR# bv@(U n) b  = U (l .|. r)
  where
    l   = shiftR_logical sz n b'
    r   = shiftL n b''

    b'  = b `mod` sz
    b'' = sz - b'
    sz  = fromInteger (natVal bv)
{-# PRIMITIVE rotateR# #-}

instance (KnownNat n, KnownNat (n + 1), KnownNat (n + 2)) => FiniteBits (Unsigned n) where
  finiteBitSize = size#

instance Resize Unsigned where
  resize     = resize#
  zeroExtend = resize#
  signExtend = resize#
  truncateB  = resize#

resize# :: KnownNat m => Unsigned n -> Unsigned m
resize# (U i) = U i
{-# PRIMITIVE_I resize# #-}

instance Default (Unsigned n) where
  def = minBound#

instance KnownNat n => Lift (Unsigned n) where
  lift u@(U i) = sigE [| fromInteger# i |] (decUnsigned (natVal u))

decUnsigned :: Integer -> TypeQ
decUnsigned n = appT (conT ''Unsigned) (litT $ numTyLit n)

instance (KnownNat n, KnownNat (1 + n), KnownNat (n + n)) =>
  SaturatingNum (Unsigned n) where
  satPlus SatWrap a b = a +# b
  satPlus w a b = case msb r of
                    0 -> resize# r
                    _ -> case w of
                           SatZero  -> minBound#
                           _        -> maxBound#
    where
      r = plus# a b

  satMin SatWrap a b = a -# b
  satMin _ a b = case msb r of
                    0 -> resize# r
                    _ -> minBound#
    where
      r = minus# a b

  satMult SatWrap a b = a *# b
  satMult w a b = case rL of
                    0 -> unpack# rR
                    _ -> case w of
                           SatZero  -> minBound#
                           _        -> maxBound#
    where
      r       = times# a b
      (rL,rR) = split r

instance KnownNat n => Arbitrary (Unsigned n) where
  arbitrary = arbitraryBoundedIntegral
  shrink    = BV.shrinkSizedUnsigned

instance KnownNat n => CoArbitrary (Unsigned n) where
  coarbitrary = coarbitraryIntegral

type instance Index   (Unsigned n) = Int
type instance IxValue (Unsigned n) = Bit
instance KnownNat n => Ixed (Unsigned n) where
  ix i f s = unpack# <$> BV.replaceBit# (pack# s) i
                     <$> f (BV.index# (pack# s) i)
