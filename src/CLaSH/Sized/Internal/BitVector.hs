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

module CLaSH.Sized.Internal.BitVector
  ( -- * Datatypes
    BitVector (..)
  , Bit
    -- * Accessors
    -- ** Length information
  , size#
  , maxIndex#
    -- * Construction
    -- ** Initialisation
  , high
  , low
  , bLit
    -- ** Concatenation
  , (++#)
    -- * Reduction
  , reduceAnd#
  , reduceOr#
  , reduceXor#
    -- * Indexing
  , index#
  , replaceBit#
  , setSlice#
  , slice#
  , split#
  , msb#
  , lsb#
    -- * Type classes
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
  , popCountBV
    -- ** Resize
  , resize#
    -- ** QuickCheck
  , shrinkSizedUnsigned
  )
where

import Control.Lens               (Index, Ixed (..), IxValue)
import Data.Bits                  (Bits (..), FiniteBits (..))
import Data.Char                  (digitToInt)
import Data.Data                  (Data)
import Data.Default               (Default (..))
import Data.Maybe                 (listToMaybe)
import GHC.Integer                (smallInteger)
import GHC.Prim                   (dataToTag#)
import GHC.TypeLits               (KnownNat, Nat, type (+), type (-), natVal)
import Language.Haskell.TH        (Q, TExp, TypeQ, appT, conT, litT, numTyLit, sigE)
import Language.Haskell.TH.Syntax (Lift(..))
import Numeric                    (readInt)
import Test.QuickCheck.Arbitrary  (Arbitrary (..), CoArbitrary (..),
                                   arbitraryBoundedIntegral,
                                   coarbitraryIntegral, shrinkIntegral)

import CLaSH.Class.Num            (ExtendingNum (..), SaturatingNum (..),
                                   SaturationMode (..))
import CLaSH.Class.Resize         (Resize (..))
import CLaSH.Promoted.Nat         (SNat, snatToInteger)
import CLaSH.Promoted.Ord         (Max)

import {-# SOURCE #-} qualified CLaSH.Sized.Vector         as V
import {-# SOURCE #-} qualified CLaSH.Sized.Internal.Index as I

{- $setup
>>> :set -XTemplateHaskell
>>> :set -XBinaryLiterals
-}

-- * Type definitions

-- | A vector of bits.
--
-- * Bit indices are descending
-- * 'Num' instance performs /unsigned/ arithmetic.
newtype BitVector (n :: Nat) =
    -- | The constructor, 'BV', and  the field, 'unsafeToInteger', are not
    -- synthesisable.
    BV { unsafeToInteger :: Integer}
  deriving Data

-- | 'Bit': a 'BitVector' of length 1
type Bit = BitVector 1

-- * Instances
instance KnownNat n => Show (BitVector n) where
  show bv = let sz = natVal bv
            in  reverse . underScore . reverse $ showBV sz (toInteger# bv) []
    where
      showBV 0 _ s = s
      showBV n v s = let (a,b) = divMod v 2
                     in  case b of
                           1 -> showBV (n - 1) a ('1':s)
                           _ -> showBV (n - 1) a ('0':s)

      underScore xs = case splitAt 5 xs of
                        ([a,b,c,d,e],rest) -> [a,b,c,d,'_'] ++ underScore (e:rest)
                        (rest,_)               -> rest

-- | Create a binary literal
--
-- >>> $$(bLit "1001") :: BitVector 4
-- 1001
-- >>> $$(bLit "1001") :: BitVector 3
-- 001
--
-- __NB__: You can also just write:
--
-- >>> 0b1001 :: BitVector 4
-- 1001
--
-- The advantage of 'bLit' is that you can use computations to create the
-- string literal:
--
-- >>> import qualified Data.List as List
-- >>> $$(bLit (List.replicate 4 '1')) :: BitVector 4
-- 1111
bLit :: KnownNat n => String -> Q (TExp (BitVector n))
bLit s = [|| fromInteger# i' ||]
  where
    i :: Maybe Integer
    i = fmap fst . listToMaybe . (readInt 2 (`elem` "01") digitToInt) $ filter (/= '_') s

    i' :: Integer
    i' = case i of
           Just j -> j
           _      -> error "Failed to parse: " s

instance KnownNat n => Eq (BitVector n) where
  (==) = eq#
  (/=) = neq#

bvmask :: Integer -> Integer -> Integer
bvmask sz i = i `mod` (shiftL 1 (fromInteger sz))
{-# INLINE bvmask #-}

eq# :: KnownNat n => BitVector n -> BitVector n -> Bool
eq# bv@(BV v1) (BV v2) = bvmask (natVal bv) v1 == bvmask (natVal bv) v2
{-# PRIMITIVE_I eq# #-}

neq# :: KnownNat n => BitVector n -> BitVector n -> Bool
neq# bv@(BV v1) (BV v2) = bvmask (natVal bv) v1 /= bvmask (natVal bv) v2
{-# PRIMITIVE_I neq# #-}

instance KnownNat n => Ord (BitVector n) where
  (<)  = lt#
  (>=) = ge#
  (>)  = gt#
  (<=) = le#

lt#,ge#,gt#,le# :: KnownNat n => BitVector n -> BitVector n -> Bool
lt# bv@(BV n) (BV m) = bvmask (natVal bv) n <  bvmask (natVal bv) m
{-# PRIMITIVE_I lt# #-}
ge# bv@(BV n) (BV m) = bvmask (natVal bv) n >= bvmask (natVal bv) m
{-# PRIMITIVE_I ge# #-}
gt# bv@(BV n) (BV m) = bvmask (natVal bv) n >  bvmask (natVal bv) m
{-# PRIMITIVE_I gt# #-}
le# bv@(BV n) (BV m) = bvmask (natVal bv) n <= bvmask (natVal bv) m
{-# PRIMITIVE_I le# #-}

-- | The functions: 'enumFrom', 'enumFromThen', 'enumFromTo', and
-- 'enumFromThenTo', are not synthesisable.
instance KnownNat n => Enum (BitVector n) where
  succ           = (+# fromInteger# 1)
  pred           = (-# fromInteger# 1)
  toEnum         = fromInteger# . toInteger
  fromEnum       = fromEnum . toInteger#
  enumFrom       = enumFrom#
  enumFromThen   = enumFromThen#
  enumFromTo     = enumFromTo#
  enumFromThenTo = enumFromThenTo#

enumFrom#       :: KnownNat n => BitVector n -> [BitVector n]
enumFromThen#   :: KnownNat n => BitVector n -> BitVector n -> [BitVector n]
enumFromTo#     :: KnownNat n => BitVector n -> BitVector n -> [BitVector n]
enumFromThenTo# :: KnownNat n => BitVector n -> BitVector n -> BitVector n
                -> [BitVector n]
enumFrom# x             = map toEnum [fromEnum x ..]
enumFromThen# x y       = map toEnum [fromEnum x, fromEnum y ..]
enumFromTo# x y         = map toEnum [fromEnum x .. fromEnum y]
enumFromThenTo# x1 x2 y = map toEnum [fromEnum x1, fromEnum x2 .. fromEnum y]
{-# PRIMITIVE_I enumFrom# #-}
{-# PRIMITIVE_I enumFromThen# #-}
{-# PRIMITIVE_I enumFromTo# #-}
{-# PRIMITIVE_I enumFromThenTo# #-}

instance KnownNat n => Bounded (BitVector n) where
  minBound = minBound#
  maxBound = maxBound#

minBound# :: BitVector n
minBound# = BV 0
{-# PRIMITIVE_I minBound# #-}

maxBound# :: KnownNat n => BitVector n
maxBound# = let res = BV (bit (fromInteger (natVal res)) - 1) in res
{-# PRIMITIVE_I maxBound# #-}

instance KnownNat n => Num (BitVector n) where
  (+)         = (+#)
  (-)         = (-#)
  (*)         = (*#)
  negate      = negate#
  abs         = id
  signum bv   = resize# (reduceOr# bv)
  fromInteger = fromInteger#

(+#),(-#),(*#) :: BitVector n -> BitVector n -> BitVector n
(+#) (BV i) (BV j) = BV (i + j)
{-# PRIMITIVE_I (+#) #-}

(-#) (BV i) (BV j) = BV (i - j)
{-# PRIMITIVE_I (-#) #-}

(*#) (BV i) (BV j) = BV (i * j)
{-# PRIMITIVE_I (*#) #-}

negate# :: BitVector n -> BitVector n
negate# (BV i) = BV (negate i)
{-# PRIMITIVE_I negate# #-}

fromInteger# :: Integer -> BitVector n
fromInteger# = BV
{-# PRIMITIVE_I fromInteger# #-}

instance ExtendingNum (BitVector m) (BitVector n) where
  type AResult (BitVector m) (BitVector n) = BitVector (Max m n + 1)
  plus  = plus#
  minus = minus#
  type MResult (BitVector m) (BitVector n) = BitVector (m + n)
  times = times#

plus#, minus# :: BitVector m -> BitVector n -> BitVector (Max m n + 1)
plus# (BV a) (BV b) = BV (a + b)
{-# PRIMITIVE_I plus# #-}

minus# (BV a) (BV b) = BV (a - b)
{-# PRIMITIVE_I minus# #-}

times# :: BitVector m -> BitVector n -> BitVector (m + n)
times# (BV a) (BV b) = BV (a * b)
{-# PRIMITIVE_I times# #-}

instance KnownNat n => Real (BitVector n) where
  toRational = toRational . toInteger#

instance KnownNat n => Integral (BitVector n) where
  quot        = quot#
  rem         = rem#
  div         = quot#
  mod         = rem#
  quotRem n d = (n `quot#` d,n `rem#` d)
  divMod  n d = (n `quot#` d,n `rem#` d)
  toInteger   = toInteger#

quot#,rem# :: BitVector n -> BitVector n -> BitVector n
quot# (BV i) (BV j) = BV (i `quot` j)
{-# PRIMITIVE_I quot# #-}
rem# (BV i) (BV j) = BV (i `rem` j)
{-# PRIMITIVE_I rem# #-}

toInteger# :: KnownNat n => BitVector n -> Integer
toInteger# bv@(BV i) = bvmask (natVal bv) i
{-# PRIMITIVE_I toInteger# #-}

instance (KnownNat n, KnownNat (n+1), KnownNat (n+2)) => Bits (BitVector n) where
  (.&.)             = and#
  (.|.)             = or#
  xor               = xor#
  complement        = complement#
  zeroBits          = 0
  bit i             = replaceBit# 0 i high
  setBit v i        = replaceBit# v i high
  clearBit v i      = replaceBit# v i low
  complementBit v i = replaceBit# v i (complement# (index# v i))
  testBit v i       = eq# (index# v i) high
  bitSizeMaybe v    = Just (size# v)
  bitSize           = size#
  isSigned _        = False
  shiftL v i        = shiftL# v i
  shiftR v i        = shiftR# v i
  rotateL v i       = rotateL# v i
  rotateR v i       = rotateR# v i
  popCount bv       = fromEnum (popCountBV (bv ++# (0 :: Bit)))

instance (KnownNat n, KnownNat (n+1), KnownNat (n+2)) => FiniteBits (BitVector n) where
  finiteBitSize = size#

reduceAnd# :: KnownNat n => BitVector n -> BitVector 1
reduceAnd# bv@(BV i) = BV (smallInteger (dataToTag# check))
  where
    check = i .&. mask == mask
    mask  = bit (fromInteger (natVal bv)) - 1
{-# PRIMITIVE reduceAnd# #-}

reduceOr# :: KnownNat n => BitVector n -> BitVector 1
reduceOr# bv@(BV i) = BV (smallInteger (dataToTag# check))
  where
    check = bvmask (natVal bv) i /= 0
{-# PRIMITIVE reduceOr# #-}

reduceXor# :: KnownNat n => BitVector n -> BitVector 1
reduceXor# bv@(BV i) = BV (toInteger (popCount (bvmask (natVal bv) i) `mod` 2))
{-# PRIMITIVE reduceXor# #-}

instance Default (BitVector n) where
  def = minBound#

-- * Accessors
-- ** Length information
size# :: KnownNat n => BitVector n -> Int
size# bv = fromInteger (natVal bv)
{-# PRIMITIVE_I size# #-}

maxIndex# :: KnownNat n => BitVector n -> Int
maxIndex# bv = fromInteger (natVal bv) - 1
{-# PRIMITIVE_I maxIndex# #-}

-- ** Indexing
index# :: KnownNat n => BitVector n -> Int -> Bit
index# bv@(BV v) i
    | i >= 0 && i < sz = BV (smallInteger
                            (dataToTag#
                            (testBit v i)))
    | otherwise        = err
  where
    sz  = fromInteger (natVal bv)
    err = error $ concat [ "(!): "
                         , show i
                         , " is out of range ["
                         , show (sz - 1)
                         , "..0]"
                         ]
{-# PRIMITIVE index# #-}

-- | MSB
msb# :: KnownNat n => BitVector n -> Bit
msb# bv@(BV v) = BV (smallInteger (dataToTag# (testBit v i)))
  where
    i = fromInteger (natVal bv - 1)
{-# PRIMITIVE_I msb# #-}

-- | LSB
lsb# :: BitVector n -> Bit
lsb# (BV v) = BV (smallInteger (dataToTag# (testBit v 0)))
{-# PRIMITIVE_I lsb# #-}

slice# :: BitVector (m + 1 + i) -> SNat m -> SNat n -> BitVector (m + 1 - n)
slice# (BV i) m n = BV (shiftR (i .&. mask) n')
  where
    m' = fromInteger (snatToInteger m)
    n' = fromInteger (snatToInteger n)

    mask = bit (m' + 1) - 1
{-# PRIMITIVE slice# #-}

-- * Constructions
-- ** Initialisation
-- | logic '1'
high :: Bit
high = BV 1
{-# PRIMITIVE_I high #-}

-- | logic '0'
low :: Bit
low = BV 0
{-# PRIMITIVE_I low #-}

-- ** Concatenation
-- | Concatenate two 'BitVector's
(++#) :: KnownNat m => BitVector n -> BitVector m -> BitVector (n + m)
(BV v1) ++# bv2@(BV v2) = BV (v1' + bvmask (natVal bv2) v2)
  where
    v1' = shiftL v1 (fromInteger (natVal bv2))
{-# PRIMITIVE (++#) #-}

-- * Modifying BitVectors
replaceBit# :: KnownNat n => BitVector n -> Int -> Bit -> BitVector n
replaceBit# bv@(BV v) i (BV b)
    | i >= 0 && i < sz = BV (if b == 1 then setBit v i else clearBit v i)
    | otherwise        = err
  where
    sz   = fromInteger (natVal bv)
    err  = error $ concat [ "replaceBit: "
                          , show i
                          , " is out of range ["
                          , show (sz - 1)
                          , "..0]"
                          ]
{-# PRIMITIVE replaceBit# #-}

setSlice# :: BitVector (m + 1 + i) -> SNat m -> SNat n -> BitVector (m + 1 - n)
          -> BitVector (m + 1 + i)
setSlice# (BV i) m n (BV j) = BV ((i .&. mask) .|. j')
  where
    m' = fromInteger (snatToInteger m)
    n' = fromInteger (snatToInteger n)

    j'   = shiftL (bvmask (snatToInteger m - snatToInteger n + 1) j) n'
    mask = complement ((bit (m' + 1)) - 1) `xor` (bit n' - 1)
{-# PRIMITIVE setSlice# #-}

split# :: KnownNat n => BitVector (m + n) -> (BitVector m, BitVector n)
split# (BV i) = (l,r)
  where
    n    = fromInteger (natVal r)
    mask = bit n - 1
    r    = BV (i .&. mask)
    l    = BV (i `shiftR` n)
{-# PRIMITIVE split# #-}

and#, or#, xor# :: BitVector n -> BitVector n -> BitVector n
and# (BV v1) (BV v2) = BV (v1 .&. v2)
{-# PRIMITIVE_I and# #-}

or# (BV v1) (BV v2) = BV (v1 .|. v2)
{-# PRIMITIVE_I or# #-}

xor# (BV v1) (BV v2) = BV (v1 `xor` v2)
{-# PRIMITIVE_I xor# #-}

complement# :: KnownNat n => BitVector n -> BitVector n
complement# (BV v1) = BV (complement v1)
{-# PRIMITIVE_I complement# #-}

shiftL#, shiftR#, rotateL#, rotateR# :: KnownNat n => BitVector n -> Int
                                     -> BitVector n
shiftL# (BV v) i
  | i < 0     = error
              $ "'shiftL undefined for negative number: " ++ show i
  | otherwise = BV (shiftL v i)
{-# PRIMITIVE shiftL# #-}

shiftR# bv@(BV v) i
  | i < 0     = error
              $ "'shiftR undefined for negative number: " ++ show i
  | otherwise = BV (shiftR_logical (fromInteger (natVal bv)) v i)
{-# PRIMITIVE shiftR# #-}

shiftR_logical :: Int -> Integer -> Int -> Integer
shiftR_logical sz n i = shiftR n i .&. (bit (sz - i) - 1)
{-# INLINE shiftR_logical #-}

rotateL# _ b | b < 0 = error "'shiftL undefined for negative numbers"
rotateL# bv@(BV n) b   = BV (l .|. r)
  where
    l    = shiftL n b'
    r    = shiftR_logical sz n b''

    b'   = b `mod` sz
    b''  = sz - b'
    sz   = fromInteger (natVal bv)
{-# PRIMITIVE rotateL# #-}

rotateR# _ b | b < 0 = error "'shiftR undefined for negative numbers"
rotateR# bv@(BV n) b   = BV (l .|. r)
  where
    l   = shiftR_logical sz n b'
    r   = shiftL n b''

    b'  = b `mod` sz
    b'' = sz - b'
    sz  = fromInteger (natVal bv)
{-# PRIMITIVE rotateR# #-}

popCountBV :: (KnownNat (n+1), KnownNat (n + 2))
           => BitVector (n+1)
           -> I.Index (n+2)
popCountBV bv = sum (V.map fromIntegral v)
  where
    v = V.bv2v bv
{-# INLINE popCountBV #-}

instance Resize BitVector where
  resize     = resize#
  zeroExtend = resize#
  signExtend = resize#
  truncateB  = resize#

resize# :: KnownNat m => BitVector n -> BitVector m
resize# (BV n) = BV n
{-# PRIMITIVE_I resize# #-}

instance KnownNat n => Lift (BitVector n) where
  lift bv@(BV i) = sigE [| fromInteger# i |] (decBitVector (natVal bv))

decBitVector :: Integer -> TypeQ
decBitVector n = appT (conT ''BitVector) (litT $ numTyLit n)

instance (KnownNat n, KnownNat (n + 1), KnownNat (n + n)) =>
  SaturatingNum (BitVector n) where
  satPlus SatWrap a b = a +# b
  satPlus w a b = case msb# r of
                   0 -> resize# r
                   _ -> case w of
                          SatZero  -> minBound#
                          _        -> maxBound#
    where
      r = plus# a b

  satMin SatWrap a b = a -# b
  satMin _ a b = case msb# r of
                   0 -> resize# r
                   _ -> minBound#
    where
      r = minus# a b

  satMult SatWrap a b = a *# b
  satMult w a b = case rL of
                     0 -> rR
                     _ -> case w of
                            SatZero  -> minBound#
                            _        -> maxBound#
    where
      r       = times# a b
      (rL,rR) = split# r

instance KnownNat n => Arbitrary (BitVector n) where
  arbitrary = arbitraryBoundedIntegral
  shrink    = shrinkSizedUnsigned

-- | 'shrink' for sized unsigned types
shrinkSizedUnsigned :: (KnownNat n, Integral (p n)) => p n -> [p n]
shrinkSizedUnsigned x | natVal x < 2 = case toInteger x of
                                         1 -> [0]
                                         _ -> []
                      -- 'shrinkIntegral' uses "`quot` 2", which for sized types
                      -- less than 2 bits wide results in a division by zero.
                      --
                      -- See: https://github.com/clash-lang/clash-compiler/issues/153
                      | otherwise    = shrinkIntegral x
{-# INLINE shrinkSizedUnsigned #-}

instance KnownNat n => CoArbitrary (BitVector n) where
  coarbitrary = coarbitraryIntegral

type instance Index   (BitVector n) = Int
type instance IxValue (BitVector n) = Bit
instance KnownNat n => Ixed (BitVector n) where
  ix i f bv = replaceBit# bv i <$> f (index# bv i)
