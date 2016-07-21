{-|
Copyright  :  (C) 2013-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MagicHash             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# LANGUAGE Unsafe #-}

{-# OPTIONS_HADDOCK show-extensions #-}

#include "primitive.h"

module CLaSH.Sized.Internal.Signed
  ( -- * Datatypes
    Signed (..)
    -- * Accessors
    -- ** Length information
  , size#
    -- * Type classes
    -- ** BitConvert
  , pack#
  , unpack#
    -- Eq
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
  , abs#
  , fromInteger#
    -- ** ExtendingNum
  , plus#
  , minus#
  , times#
    -- ** Integral
  , quot#
  , rem#
  , div#
  , mod#
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
  , truncateB#
    -- ** SaturatingNum
  , minBoundSym#
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
                                       coarbitraryIntegral, shrinkIntegral)

import CLaSH.Class.BitPack            (BitPack (..))
import CLaSH.Class.Num                (ExtendingNum (..), SaturatingNum (..),
                                       SaturationMode (..))
import CLaSH.Class.Resize             (Resize (..))
import CLaSH.Prelude.BitIndex         ((!), msb, replaceBit, split)
import CLaSH.Prelude.BitReduction     (reduceAnd, reduceOr)
import CLaSH.Promoted.Ord             (Max)
import CLaSH.Sized.Internal.BitVector (BitVector (..), Bit, (++#), high, low)
import qualified CLaSH.Sized.Internal.BitVector as BV

-- | Arbitrary-width signed integer represented by @n@ bits, including the sign
-- bit.
--
-- Uses standard 2-complements representation. Meaning that, given @n@ bits,
-- a 'Signed' @n@ number has a range of: [-(2^(@n@-1)) .. 2^(@n@-1)-1]
--
-- __NB__: The 'Num' operators perform @wrap-around@ on overflow. If you want
-- saturation on overflow, check out the 'SaturatingNum' class.
--
-- >>>  maxBound :: Signed 3
-- 3
-- >>> minBound :: Signed 3
-- -4
-- >>> read (show (minBound :: Signed 3)) :: Signed 3
-- -4
-- >>> 1 + 2 :: Signed 3
-- 3
-- >>> 2 + 3 :: Signed 3
-- -3
-- >>> (-2) + (-3) :: Signed 3
-- 3
-- >>> 2 * 3 :: Signed 4
-- 6
-- >>> 2 * 4 :: Signed 4
-- -8
-- >>> (2 :: Signed 3) `times` (4 :: Signed 4) :: Signed 7
-- 8
-- >>> (2 :: Signed 3) `plus` (3 :: Signed 3) :: Signed 4
-- 5
-- >>> (-2 :: Signed 3) `plus` (-3 :: Signed 3) :: Signed 4
-- -5
-- >>> satPlus SatSymmetric 2 3 :: Signed 3
-- 3
-- >>> satPlus SatSymmetric (-2) (-3) :: Signed 3
-- -3
newtype Signed (n :: Nat) =
    -- | The constructor, 'S', and the field, 'unsafeToInteger', are not
    -- synthesisable.
    S { unsafeToInteger :: Integer}
  deriving Data

{-# PRIMITIVE_I size# #-}
size# :: KnownNat n => Signed n -> Int
size# bv = fromInteger (natVal bv)

instance KnownNat n => Show (Signed n) where
  showsPrec p s = showsPrec p (toInteger# s)
  show s = show (toInteger# s)
  -- We cannot say:
  --
  -- > show (S i) = show i
  --
  -- Because GHC translates that to a cast from Signed to Integer,
  -- which the CLaSH compiler can (currently) not handle.

-- | None of the 'Read' class' methods are synthesisable.
instance KnownNat n => Read (Signed n) where
  readPrec = fromIntegral <$> (readPrec :: ReadPrec Int)

instance KnownNat n => BitPack (Signed n) where
  type BitSize (Signed n) = n
  pack   = pack#
  unpack = unpack#

{-# PRIMITIVE_I pack# #-}
pack# :: Signed n -> BitVector n
pack# (S i) = BV i

{-# PRIMITIVE_I unpack# #-}
unpack# :: BitVector n -> Signed n
unpack# (BV i) = S i

instance KnownNat n => Eq (Signed n) where
  (==) = eq#
  (/=) = neq#

smask :: Integer -> Integer -> Integer
smask sz i
  | sz == 0   = 0
  | otherwise = res
  where
    mask = shiftL 1 (fromInteger sz - 1)
    res  = case divMod i mask of
              (s,i') | even s    -> i'
                     | otherwise -> (i' - mask)
{-# INLINE smask #-}

eq# :: KnownNat n => Signed n -> Signed n -> Bool
eq# s@(S v1) (S v2) = smask (natVal s) v1 == smask (natVal s) v2
{-# PRIMITIVE_I eq# #-}

neq# :: KnownNat n => Signed n -> Signed n -> Bool
neq# s@(S v1) (S v2) = smask (natVal s) v1 /= smask (natVal s) v2
{-# PRIMITIVE_I neq# #-}

instance KnownNat n => Ord (Signed n) where
  (<)  = lt#
  (>=) = ge#
  (>)  = gt#
  (<=) = le#

lt#,ge#,gt#,le# :: KnownNat n => Signed n -> Signed n -> Bool
lt# s@(S n) (S m) = smask (natVal s) n <  smask (natVal s) m
{-# PRIMITIVE_I lt# #-}
ge# s@(S n) (S m) = smask (natVal s) n >= smask (natVal s)  m
{-# PRIMITIVE_I ge# #-}
gt# s@(S n) (S m) = smask (natVal s) n >  smask (natVal s) m
{-# PRIMITIVE_I gt# #-}
le# s@(S n) (S m) = smask (natVal s) n <= smask (natVal s)  m
{-# PRIMITIVE_I le# #-}

-- | The functions: 'enumFrom', 'enumFromThen', 'enumFromTo', and
-- 'enumFromThenTo', are not synthesisable.
instance KnownNat n => Enum (Signed n) where
  succ           = (+# fromInteger# 1)
  pred           = (-# fromInteger# 1)
  toEnum         = fromInteger# . toInteger
  fromEnum       = fromEnum . toInteger#
  enumFrom       = enumFrom#
  enumFromThen   = enumFromThen#
  enumFromTo     = enumFromTo#
  enumFromThenTo = enumFromThenTo#

enumFrom#       :: KnownNat n => Signed n -> [Signed n]
enumFromThen#   :: KnownNat n => Signed n -> Signed n -> [Signed n]
enumFromTo#     :: KnownNat n => Signed n -> Signed n -> [Signed n]
enumFromThenTo# :: KnownNat n => Signed n -> Signed n -> Signed n -> [Signed n]
enumFrom# x             = map toEnum [fromEnum x ..]
enumFromThen# x y       = map toEnum [fromEnum x, fromEnum y ..]
enumFromTo# x y         = map toEnum [fromEnum x .. fromEnum y]
enumFromThenTo# x1 x2 y = map toEnum [fromEnum x1, fromEnum x2 .. fromEnum y]
{-# PRIMITIVE enumFrom# #-}
{-# PRIMITIVE enumFromThen# #-}
{-# PRIMITIVE enumFromTo# #-}
{-# PRIMITIVE enumFromThenTo# #-}

instance KnownNat n => Bounded (Signed n) where
  minBound = minBound#
  maxBound = maxBound#

minBound#,maxBound# :: KnownNat n => Signed n
minBound# = let sz  = natVal res
                res | sz == 0   = S 0
                    | otherwise = S (negate (shiftL 1 (fromInteger sz - 1)))
            in res
{-# PRIMITIVE minBound# #-}
maxBound# = let sz  = natVal res
                res | sz == 0   = S 0
                    | otherwise = S (shiftL 1 (fromInteger sz - 1) - 1)
            in res
{-# PRIMITIVE maxBound# #-}

-- | Operators do @wrap-around@ on overflow
instance KnownNat n => Num (Signed n) where
  (+)         = (+#)
  (-)         = (-#)
  (*)         = (*#)
  negate      = negate#
  abs         = abs#
  signum s    = if s < 0 then (-1) else
                   if s > 0 then 1 else 0
  fromInteger = fromInteger#

(+#), (-#), (*#) :: Signed n -> Signed n -> Signed n
(S a) +# (S b) = S (a + b)
{-# PRIMITIVE_I (+#) #-}

(S a) -# (S b) = S (a - b)
{-# PRIMITIVE_I (-#) #-}

(S a) *# (S b) = S (a * b)
{-# PRIMITIVE_I (*#) #-}

negate#,abs# :: Signed n -> Signed n
negate# (S n) = S (negate n)
{-# PRIMITIVE_I negate# #-}

abs# (S n) = S (abs n)
{-# PRIMITIVE_I abs# #-}

fromInteger# :: Integer -> Signed (n :: Nat)
fromInteger# = S
{-# PRIMITIVE_I fromInteger# #-}

instance ExtendingNum (Signed m) (Signed n) where
  type AResult (Signed m) (Signed n) = Signed (1 + Max m n)
  plus  = plus#
  minus = minus#
  type MResult (Signed m) (Signed n) = Signed (m + n)
  times = times#

plus#, minus# :: Signed m -> Signed n -> Signed (1 + Max m n)
plus# (S a) (S b) = S (a + b)
{-# PRIMITIVE_I plus# #-}

minus# (S a) (S b) = S (a - b)
{-# PRIMITIVE_I minus# #-}

times# :: Signed m -> Signed n -> Signed (m + n)
times# (S a) (S b) = S (a * b)
{-# PRIMITIVE_I times# #-}

instance KnownNat n => Real (Signed n) where
  toRational = toRational . toInteger#

instance KnownNat n => Integral (Signed n) where
  quot        = quot#
  rem         = rem#
  div         = div#
  mod         = mod#
  quotRem n d = (n `quot#` d,n `rem#` d)
  divMod  n d = (n `div#`  d,n `mod#` d)
  toInteger   = toInteger#

quot#,rem# :: Signed n -> Signed n -> Signed n
quot# (S a) (S b) = S (a `quot` b)
{-# PRIMITIVE_I quot# #-}
rem# (S a) (S b) = S (a `rem` b)
{-# PRIMITIVE_I rem# #-}

div#,mod# :: Signed n -> Signed n -> Signed n
div# (S a) (S b) = S (a `div` b)
{-# PRIMITIVE_I div# #-}
mod# (S a) (S b) = S (a `mod` b)
{-# PRIMITIVE_I mod# #-}

toInteger# :: KnownNat n => Signed n -> Integer
toInteger# s@(S n) = smask (natVal s) n
{-# PRIMITIVE_I toInteger# #-}

instance (KnownNat n, KnownNat (n + 1), KnownNat (n + 2)) => Bits (Signed n) where
  (.&.)             = and#
  (.|.)             = or#
  xor               = xor#
  complement        = complement#
  zeroBits          = 0
  bit i             = replaceBit i high 0
  setBit v i        = replaceBit i high v
  clearBit v i      = replaceBit i low  v
  complementBit v i = replaceBit i (BV.complement# (v ! i)) v
  testBit v i       = v ! i == 1
  bitSizeMaybe v    = Just (size# v)
  bitSize           = size#
  isSigned _        = True
  shiftL v i        = shiftL# v i
  shiftR v i        = shiftR# v i
  rotateL v i       = rotateL# v i
  rotateR v i       = rotateR# v i
  popCount s        = popCount (pack# s)

and#,or#,xor# :: KnownNat n => Signed n -> Signed n -> Signed n
and# (S a) (S b) = S (a .&. b)
{-# PRIMITIVE_I and# #-}
or# (S a) (S b)  = S (a .|. b)
{-# PRIMITIVE_I or# #-}
xor# (S a) (S b) = S (xor a b)
{-# PRIMITIVE_I xor# #-}

complement# :: KnownNat n => Signed n -> Signed n
complement# (S a) = S (complement a)
{-# PRIMITIVE_I complement# #-}

shiftL#,shiftR#,rotateL#,rotateR# :: KnownNat n => Signed n -> Int -> Signed n
shiftL# _ b | b < 0  = error "'shiftL undefined for negative numbers"
shiftL# (S n) b      = S (shiftL n b)
{-# PRIMITIVE shiftL# #-}
shiftR# _ b | b < 0  = error "'shiftR undefined for negative numbers"
shiftR# s@(S n) b    = S (shiftR (smask (natVal s) n) b)
{-# PRIMITIVE shiftR# #-}
rotateL# _ b | b < 0 = error "'shiftL undefined for negative numbers"
rotateL# s@(S n) b   = S (l .|. r)
  where
    l    = shiftL n b'
    r    = shiftR n b'' .&. mask
    mask = 2 ^ b' - 1

    b'   = b `mod` sz
    b''  = sz - b'
    sz   = fromInteger (natVal s)
{-# PRIMITIVE rotateL# #-}

rotateR# _ b | b < 0 = error "'shiftR undefined for negative numbers"
rotateR# s@(S n) b   = S (l .|. r)
  where
    l    = shiftR n b' .&. mask
    r    = shiftL n b''
    mask = 2 ^ b'' - 1

    b'  = b `mod` sz
    b'' = sz - b'
    sz  = fromInteger (natVal s)
{-# PRIMITIVE rotateR# #-}

instance (KnownNat n, KnownNat (n + 1), KnownNat (n + 2)) => FiniteBits (Signed n) where
  finiteBitSize = size#

instance Resize Signed where
  resize       = resize#
  extend       = resize#
  zeroExtend s = unpack# (0 ++# pack s)
  signExtend   = resize#
  truncateB    = truncateB#

resize# :: (KnownNat n, KnownNat m) => Signed n -> Signed m
resize# s@(S i) | n <= m    = extended
                | m == 0    = S 0
                | otherwise = truncated
  where
    n = fromInteger (natVal s)
    m = fromInteger (natVal extended)

    extended  = S i

    mask      = (2 ^ (m - 1)) - 1
    sign      = 2 ^ (m - 1)
    i'        = i .&. mask
    truncated = if testBit i (n - 1)
                   then S (i' .|. sign)
                   else S i'
{-# PRIMITIVE resize# #-}

truncateB# :: Signed (m + n) -> Signed m
truncateB# (S n) = S n
{-# PRIMITIVE_I truncateB# #-}

instance KnownNat n => Default (Signed n) where
  def = fromInteger# 0

instance KnownNat n => Lift (Signed n) where
  lift s@(S i) = sigE [| fromInteger# i |] (decSigned (natVal s))

decSigned :: Integer -> TypeQ
decSigned n = appT (conT ''Signed) (litT $ numTyLit n)

instance (KnownNat n, KnownNat (1 + n), KnownNat (n + n)) =>
  SaturatingNum (Signed n) where
  satPlus SatWrap a b = a +# b
  satPlus w a b = case msb r `xor` msb r' of
                     0 -> unpack# r'
                     _ -> case msb a .&. msb b of
                            1 -> case w of
                                   SatBound     -> minBound#
                                   SatSymmetric -> minBoundSym#
                                   _            -> fromInteger# 0
                            _ -> case w of
                                   SatZero -> fromInteger# 0
                                   _       -> maxBound#
    where
      r      = plus# a b
      (_,r') = split r

  satMin SatWrap a b = a -# b
  satMin w a b = case msb r `xor` msb r' of
                     0 -> unpack# r'
                     _ -> case msb a ++# msb b of
                            2 -> case w of
                                   SatBound     -> minBound#
                                   SatSymmetric -> minBoundSym#
                                   _            -> fromInteger# 0
                            _ -> case w of
                                   SatZero -> fromInteger# 0
                                   _       -> maxBound#
    where
      r      = minus# a b
      (_,r') = split r


  satMult SatWrap a b = a *# b
  satMult w a b = case overflow of
                     1 -> unpack# rR
                     _ -> case msb rL of
                            0 -> case w of
                                   SatZero -> fromInteger# 0
                                   _       -> maxBound#
                            _ -> case w of
                                   SatBound     -> minBound#
                                   SatSymmetric -> minBoundSym#
                                   _            -> fromInteger# 0
    where
      overflow = complement (reduceOr (msb rR ++# pack rL)) .|.
                            reduceAnd (msb rR ++# pack rL)
      r        = times# a b
      (rL,rR)  = split r

minBoundSym# :: KnownNat n => Signed n
minBoundSym# = minBound# +# fromInteger# 1

instance KnownNat n => Arbitrary (Signed n) where
  arbitrary = arbitraryBoundedIntegral
  shrink    = shrinkSizedSigned

shrinkSizedSigned :: (KnownNat n, Integral (p n)) => p n -> [p n]
shrinkSizedSigned x | natVal x < 2 = case toInteger x of
                                       0 -> []
                                       _ -> [0]
                    -- 'shrinkIntegral' uses "`quot` 2", which for sized types
                    -- less than 2 bits wide results in a division by zero.
                    --
                    -- See: https://github.com/clash-lang/clash-compiler/issues/153
                    | otherwise    = shrinkIntegral x
{-# INLINE shrinkSizedSigned #-}

instance KnownNat n => CoArbitrary (Signed n) where
  coarbitrary = coarbitraryIntegral

type instance Index   (Signed n) = Int
type instance IxValue (Signed n) = Bit
instance KnownNat n => Ixed (Signed n) where
  ix i f s = unpack# <$> BV.replaceBit# (pack# s) i
                     <$> f (BV.index# (pack# s) i)
