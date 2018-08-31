{-|
Copyright  :  (C) 2013-2016, University of Twente,
                  2016     , Myrtle Software Ltd
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MagicHash                  #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# LANGUAGE Unsafe #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}
{-# OPTIONS_HADDOCK show-extensions not-home #-}

module Clash.Sized.Internal.BitVector
  ( -- * Bit
    Bit (..)
    -- ** Construction
  , high
  , low
    -- ** Type classes
    -- *** Eq
  , eq##
  , neq##
    -- *** Ord
  , lt##
  , ge##
  , gt##
  , le##
    -- *** Num
  , fromInteger##
    -- *** Bits
  , and##
  , or##
  , xor##
  , complement##
    -- *** BitPack
  , pack#
  , unpack#
    -- * BitVector
  , BitVector (..)
    -- ** Accessors
  , size#
  , maxIndex#
    -- ** Construction
  , bLit
  , undefined#
    -- ** Concatenation
  , (++#)
    -- ** Reduction
  , reduceAnd#
  , reduceOr#
  , reduceXor#
    -- ** Indexing
  , index#
  , replaceBit#
  , setSlice#
  , slice#
  , split#
  , msb#
  , lsb#
    -- ** Type classes
    -- **** Eq
  , eq#
  , neq#
  , isLike
    -- *** Ord
  , lt#
  , ge#
  , gt#
  , le#
    -- *** Enum (not synthesisable)
  , enumFrom#
  , enumFromThen#
  , enumFromTo#
  , enumFromThenTo#
    -- *** Bounded
  , minBound#
  , maxBound#
    -- *** Num
  , (+#)
  , (-#)
  , (*#)
  , negate#
  , fromInteger#
    -- *** ExtendingNum
  , plus#
  , minus#
  , times#
    -- *** Integral
  , quot#
  , rem#
  , toInteger#
    -- *** Bits
  , and#
  , or#
  , xor#
  , complement#
  , shiftL#
  , shiftR#
  , rotateL#
  , rotateR#
  , popCountBV
    -- *** FiniteBits
  , countLeadingZerosBV
  , countTrailingZerosBV
    -- *** Resize
  , resize#
    -- *** QuickCheck
  , shrinkSizedUnsigned
  -- ** Other
  , undefError
  , checkUnpackUndef
  )
where

import Control.DeepSeq            (NFData (..))
import Control.Lens               (Index, Ixed (..), IxValue)
import Data.Bits                  (Bits (..), FiniteBits (..))
import Data.Data                  (Data)
import Data.Default.Class         (Default (..))
import Data.Proxy                 (Proxy (..))
import Data.Typeable              (Typeable, typeOf)
import GHC.Integer                (smallInteger)
import GHC.Prim                   (dataToTag#)
import GHC.Stack                  (HasCallStack, withFrozenCallStack)
import GHC.TypeLits               (KnownNat, Nat, type (+), type (-), natVal)
import GHC.TypeLits.Extra         (Max)
import Language.Haskell.TH        (Q, TExp, TypeQ, appT, conT, litT, numTyLit, sigE)
import Language.Haskell.TH.Syntax (Lift(..))
import Test.QuickCheck.Arbitrary  (Arbitrary (..), CoArbitrary (..),
                                   arbitraryBoundedIntegral,
                                   coarbitraryIntegral, shrinkIntegral)

import Clash.Class.Num            (ExtendingNum (..), SaturatingNum (..),
                                   SaturationMode (..))
import Clash.Class.Resize         (Resize (..))
import Clash.Promoted.Nat         (SNat, snatToInteger, snatToNum)
import Clash.XException
  (ShowX (..), Undefined, errorX, showsPrecXWith)

import {-# SOURCE #-} qualified Clash.Sized.Vector         as V
import {-# SOURCE #-} qualified Clash.Sized.Internal.Index as I
import                qualified Data.List                  as L

{- $setup
>>> :set -XTemplateHaskell
>>> :set -XBinaryLiterals
-}

-- * Type definitions

-- | A vector of bits.
--
-- * Bit indices are descending
-- * 'Num' instance performs /unsigned/ arithmetic.
data BitVector (n :: Nat) =
    -- | The constructor, 'BV', and  the field, 'unsafeToInteger', are not
    -- synthesisable.
    BV { unsafeMask      :: Integer
       , unsafeToInteger :: Integer
       }
  deriving (Data,Undefined)

-- * Bit

-- | Bit
data Bit =
  -- | The constructor, 'Bit', and  the field, 'unsafeToInteger#', are not
  -- synthesisable.
  Bit { unsafeMask#      :: Integer
      , unsafeToInteger# :: Integer
      }
  deriving (Data,Undefined)

-- * Constructions
-- ** Initialisation
{-# NOINLINE high #-}
-- | logic '1'
high :: Bit
high = Bit 0 1

{-# NOINLINE low #-}
-- | logic '0'
low :: Bit
low = Bit 0 0

-- ** Instances
instance NFData Bit where
  rnf (Bit m i) = rnf m `seq` rnf i `seq` ()
  {-# NOINLINE rnf #-}

instance Show Bit where
  show (Bit 0 b) =
    case b of
      0 -> "0"
      _ -> "1"
  show (Bit _ _) = "."

instance ShowX Bit where
  showsPrecX = showsPrecXWith showsPrec

instance Lift Bit where
  lift (Bit m i) = [| fromInteger## m i |]
  {-# NOINLINE lift #-}

instance Eq Bit where
  (==) = eq##
  (/=) = neq##

eq## :: Bit -> Bit -> Bool
eq## b1 b2 = eq# (pack# b1) (pack# b2)
{-# NOINLINE eq## #-}

neq## :: Bit -> Bit -> Bool
neq## b1 b2 = neq# (pack# b1) (pack# b2)
{-# NOINLINE neq## #-}

instance Ord Bit where
  (<)  = lt##
  (<=) = le##
  (>)  = gt##
  (>=) = ge##

lt##,ge##,gt##,le## :: Bit -> Bit -> Bool
lt## b1 b2 = lt# (pack# b1) (pack# b2)
{-# NOINLINE lt## #-}
ge## b1 b2 = ge# (pack# b1) (pack# b2)
{-# NOINLINE ge## #-}
gt## b1 b2 = gt# (pack# b1) (pack# b2)
{-# NOINLINE gt## #-}
le## b1 b2 = le# (pack# b1) (pack# b2)
{-# NOINLINE le## #-}

instance Enum Bit where
  toEnum     = fromInteger## 0 . toInteger
  fromEnum b = if eq## b low then 0 else 1

instance Bounded Bit where
  minBound = low
  maxBound = high

instance Default Bit where
  def = low

instance Num Bit where
  (+)         = xor##
  (-)         = xor##
  (*)         = and##
  negate      = complement##
  abs         = id
  signum b    = b
  fromInteger = fromInteger## 0

fromInteger## :: Integer -> Integer -> Bit
fromInteger## m i = Bit (m `mod` 2) (i `mod` 2)
{-# NOINLINE fromInteger## #-}

instance Real Bit where
  toRational b = if eq## b low then 0 else 1

instance Integral Bit where
  quot    a _ = a
  rem     _ _ = low
  div     a _ = a
  mod     _ _ = low
  quotRem n _ = (n,low)
  divMod  n _ = (n,low)
  toInteger b = if eq## b low then 0 else 1

instance Bits Bit where
  (.&.)             = and##
  (.|.)             = or##
  xor               = xor##
  complement        = complement##
  zeroBits          = low
  bit i             = if i == 0 then high else low
  setBit _ i        = if i == 0 then high else low
  clearBit _ i      = if i == 0 then low  else high
  complementBit b i = if i == 0 then complement## b else b
  testBit b i       = if i == 0 then eq## b high else False
  bitSizeMaybe _    = Just 1
  bitSize _         = 1
  isSigned _        = False
  shiftL b i        = if i == 0 then b else low
  shiftR b i        = if i == 0 then b else low
  rotateL b _       = b
  rotateR b _       = b
  popCount b        = if eq## b low then 0 else 1

instance FiniteBits Bit where
  finiteBitSize _      = 1
  countLeadingZeros b  = if eq## b low then 1 else 0
  countTrailingZeros b = if eq## b low then 1 else 0

and##, or##, xor## :: Bit -> Bit -> Bit
and## b1 b2 = unpack# $ and# (pack# b1) (pack# b2)
{-# NOINLINE and## #-}

or## b1 b2 = unpack# $ or# (pack# b1) (pack# b2)
{-# NOINLINE or## #-}

xor## b1 b2 = unpack# $ xor# (pack# b1) (pack# b2)
{-# NOINLINE xor## #-}

complement## :: Bit -> Bit
complement## = unpack# . complement# . pack#
{-# NOINLINE complement## #-}

-- *** BitPack
pack# :: Bit -> BitVector 1
pack# (Bit m b) = BV m b
{-# NOINLINE pack# #-}

unpack# :: BitVector 1 -> Bit
unpack# (BV m b) = Bit m b
{-# NOINLINE unpack# #-}

-- * Instances
instance NFData (BitVector n) where
  rnf (BV i m) = rnf i `seq` rnf m `seq` ()
  {-# NOINLINE rnf #-}
  -- NOINLINE is needed so that Clash doesn't trip on the "BitVector ~# Integer"
  -- coercion

instance KnownNat n => Show (BitVector n) where
  show bv@(BV msk i) = reverse . underScore . reverse $ showBV (natVal bv) msk i []
    where
      showBV 0 _ _ s = s
      showBV n m v s = let (v',vBit) = divMod v 2
                           (m',mBit) = divMod m 2
                       in  case (mBit,vBit) of
                           (0,0) -> showBV (n - 1) m' v' ('0':s)
                           (0,_) -> showBV (n - 1) m' v' ('1':s)
                           _     -> showBV (n - 1) m' v' ('.':s)

      underScore xs = case splitAt 5 xs of
                        ([a,b,c,d,e],rest) -> [a,b,c,d,'_'] ++ underScore (e:rest)
                        (rest,_)               -> rest
  {-# NOINLINE show #-}

instance KnownNat n => ShowX (BitVector n) where
  showsPrecX = showsPrecXWith showsPrec

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
--
-- Also 'bLit' can handle don't care bits:
--
-- >>> $$(bLit "1.0.") :: BitVector 4
-- 1.0.
bLit :: forall n. KnownNat n => String -> Q (TExp (BitVector n))
bLit s = [|| fromInteger# m i ||]
  where
    bv :: BitVector n
    bv = read# s

    m,i :: Integer
    BV m i = bv

read# :: KnownNat n => String -> BitVector n
read# cs = BV m v
  where
    (vs,ms) = unzip . map readBit . filter (/= '_') $ cs
    combineBits = foldl (\b a -> b*2+a) 0
    v = combineBits vs
    m = combineBits ms
    readBit c = case c of
      '0' -> (0,0)
      '1' -> (1,0)
      '.' -> (0,1)
      _   -> error $ "Clash.Sized.Internal.bLit: unknown character: " ++ show c ++ " in input: " ++ cs


instance KnownNat n => Eq (BitVector n) where
  (==) = eq#
  (/=) = neq#

{-# NOINLINE eq# #-}
eq# :: KnownNat n => BitVector n -> BitVector n -> Bool
eq# (BV 0 v1) (BV 0 v2 ) = v1 == v2
eq# bv1 bv2 = undefErrorI "==" bv1 bv2

{-# NOINLINE neq# #-}
neq# :: KnownNat n => BitVector n -> BitVector n -> Bool
neq# (BV 0 v1) (BV 0 v2) = v1 /= v2
neq# bv1 bv2 = undefErrorI "/=" bv1 bv2

instance KnownNat n => Ord (BitVector n) where
  (<)  = lt#
  (>=) = ge#
  (>)  = gt#
  (<=) = le#

lt#,ge#,gt#,le# :: KnownNat n => BitVector n -> BitVector n -> Bool
{-# NOINLINE lt# #-}
lt# (BV 0 n) (BV 0 m) = n < m
lt# bv1 bv2 = undefErrorI "<" bv1 bv2
{-# NOINLINE ge# #-}
ge# (BV 0 n) (BV 0 m) = n >= m
ge# bv1 bv2 = undefErrorI ">=" bv1 bv2
{-# NOINLINE gt# #-}
gt# (BV 0 n) (BV 0 m) = n > m
gt# bv1 bv2 = undefErrorI ">" bv1 bv2
{-# NOINLINE le# #-}
le# (BV 0 n) (BV 0 m) = n <= m
le#  bv1 bv2 = undefErrorI "<=" bv1 bv2

-- | The functions: 'enumFrom', 'enumFromThen', 'enumFromTo', and
-- 'enumFromThenTo', are not synthesisable.
instance KnownNat n => Enum (BitVector n) where
  succ           = (+# fromInteger# 0 1)
  pred           = (-# fromInteger# 0 1)
  toEnum         = fromInteger# 0 . toInteger
  fromEnum       = fromEnum . toInteger#
  enumFrom       = enumFrom#
  enumFromThen   = enumFromThen#
  enumFromTo     = enumFromTo#
  enumFromThenTo = enumFromThenTo#

{-# NOINLINE enumFrom# #-}
{-# NOINLINE enumFromThen# #-}
{-# NOINLINE enumFromTo# #-}
{-# NOINLINE enumFromThenTo# #-}
enumFrom#       :: KnownNat n => BitVector n -> [BitVector n]
enumFromThen#   :: KnownNat n => BitVector n -> BitVector n -> [BitVector n]
enumFromTo#     :: KnownNat n => BitVector n -> BitVector n -> [BitVector n]
enumFromThenTo# :: KnownNat n => BitVector n -> BitVector n -> BitVector n -> [BitVector n]

enumFrom# (BV 0 x)                           = map (fromInteger_INLINE 0) [x ..]
enumFrom# bv
  = undefErrorU "enumFrom" bv

enumFromThen# (BV 0 x) (BV 0 y)              = map (fromInteger_INLINE 0) [x, y ..]
enumFromThen# bv1 bv2
  = undefErrorP "enumFromThen" bv1 bv2

enumFromTo# (BV 0 x) (BV 0 y)                = map (BV 0) [x .. y]
enumFromTo# bv1 bv2
  = undefErrorP "enumFromTo" bv1 bv2

enumFromThenTo# (BV 0 x1) (BV 0 x2) (BV 0 y) = map (BV 0) [x1, x2 .. y]
enumFromThenTo# bv1 bv2 bv3
  = undefErrorP3 "enumFromTo" bv1 bv2 bv3


instance KnownNat n => Bounded (BitVector n) where
  minBound = minBound#
  maxBound = maxBound#

{-# NOINLINE minBound# #-}
minBound# :: BitVector n
minBound# = BV 0 0

{-# NOINLINE maxBound# #-}
maxBound# :: forall n . KnownNat n => BitVector n
maxBound# = let m = 1 `shiftL` fromInteger (natVal (Proxy @n))
            in  BV 0 (m-1)

instance KnownNat n => Num (BitVector n) where
  (+)         = (+#)
  (-)         = (-#)
  (*)         = (*#)
  negate      = negate#
  abs         = id
  signum bv   = resize# (pack# (reduceOr# bv))
  fromInteger = fromInteger# 0

(+#),(-#),(*#) :: forall n . KnownNat n => BitVector n -> BitVector n -> BitVector n
{-# NOINLINE (+#) #-}
(+#) (BV 0 i) (BV 0 j) =
  let m = 1 `shiftL` fromInteger (natVal (Proxy @n))
      z = i + j
  in  if z >= m then BV 0 (z - m) else BV 0 z
(+#) bv1 bv2 = undefErrorI "+" bv1 bv2

{-# NOINLINE (-#) #-}
(-#) (BV 0 i) (BV 0 j) =
  let m = 1 `shiftL` fromInteger (natVal (Proxy @n))
      z = i - j
  in  if z < 0 then BV 0 (m + z) else BV 0 z
(-#) bv1 bv2 = undefErrorI "-" bv1 bv2

{-# NOINLINE (*#) #-}
(*#) (BV 0 i) (BV 0 j) = fromInteger_INLINE 0 (i * j)
(*#) bv1 bv2 = undefErrorI "*" bv1 bv2

{-# NOINLINE negate# #-}
negate# :: forall n . KnownNat n => BitVector n -> BitVector n
negate# (BV 0 0) = BV 0 0
negate# (BV 0 i) = BV 0 (sz - i)
  where
    sz = 1 `shiftL` fromInteger (natVal (Proxy @n))
negate# bv = undefErrorU "negate" bv

{-# NOINLINE fromInteger# #-}
fromInteger# :: KnownNat n => Integer -> Integer -> BitVector n
fromInteger# = fromInteger_INLINE

{-# INLINE fromInteger_INLINE #-}
fromInteger_INLINE :: forall n . KnownNat n => Integer -> Integer -> BitVector n
fromInteger_INLINE m i = sz `seq` BV (m `mod` sz) (i `mod` sz)
  where
    sz = 1 `shiftL` fromInteger (natVal (Proxy @n))

instance (KnownNat m, KnownNat n) => ExtendingNum (BitVector m) (BitVector n) where
  type AResult (BitVector m) (BitVector n) = BitVector (Max m n + 1)
  add  = plus#
  sub = minus#
  type MResult (BitVector m) (BitVector n) = BitVector (m + n)
  mul = times#

{-# NOINLINE plus# #-}
plus# :: (KnownNat m, KnownNat n) => BitVector m -> BitVector n -> BitVector (Max m n + 1)
plus# (BV 0 a) (BV 0 b) = BV 0 (a + b)
plus# bv1 bv2 = undefErrorP "plus" bv1 bv2

{-# NOINLINE minus# #-}
minus# :: forall m n . (KnownNat m, KnownNat n) => BitVector m -> BitVector n
                                                -> BitVector (Max m n + 1)
minus# (BV 0 a) (BV 0 b) =
  let sz   = fromInteger (natVal (Proxy @(Max m n + 1)))
      mask = 1 `shiftL` sz
      z    = a - b
  in  if z < 0 then BV 0 (mask + z) else BV 0 z
minus# bv1 bv2 = undefErrorP "minus" bv1 bv2

{-# NOINLINE times# #-}
times# :: (KnownNat m, KnownNat n) => BitVector m -> BitVector n -> BitVector (m + n)
times# (BV 0 a) (BV 0 b) = BV 0 (a * b)
times# bv1 bv2 = undefErrorP "times" bv1 bv2

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

quot#,rem# :: KnownNat n => BitVector n -> BitVector n -> BitVector n
{-# NOINLINE quot# #-}
quot# (BV 0 i) (BV 0 j) = BV 0 (i `quot` j)
quot# bv1 bv2 = undefErrorP "quot" bv1 bv2
{-# NOINLINE rem# #-}
rem# (BV 0 i) (BV 0 j) = BV 0 (i `rem` j)
rem# bv1 bv2 = undefErrorP "rem" bv1 bv2

{-# NOINLINE toInteger# #-}
toInteger# :: KnownNat n => BitVector n -> Integer
toInteger# (BV 0 i) = i
toInteger# bv = undefErrorU "toInteger" bv

instance KnownNat n => Bits (BitVector n) where
  (.&.)             = and#
  (.|.)             = or#
  xor               = xor#
  complement        = complement#
  zeroBits          = 0
  bit i             = replaceBit# 0 i high
  setBit v i        = replaceBit# v i high
  clearBit v i      = replaceBit# v i low
  complementBit v i = replaceBit# v i (complement## (index# v i))
  testBit v i       = eq## (index# v i) high
  bitSizeMaybe v    = Just (size# v)
  bitSize           = size#
  isSigned _        = False
  shiftL v i        = shiftL# v i
  shiftR v i        = shiftR# v i
  rotateL v i       = rotateL# v i
  rotateR v i       = rotateR# v i
  popCount bv       = fromInteger (I.toInteger# (popCountBV (bv ++# (0 :: BitVector 1))))

instance KnownNat n => FiniteBits (BitVector n) where
  finiteBitSize       = size#
  countLeadingZeros   = fromInteger . I.toInteger# . countLeadingZerosBV
  countTrailingZeros  = fromInteger . I.toInteger# . countTrailingZerosBV

countLeadingZerosBV :: KnownNat n => BitVector n -> I.Index (n+1)
countLeadingZerosBV = V.foldr (\l r -> if eq## l low then 1 + r else 0) 0 . V.bv2v
{-# INLINE countLeadingZerosBV #-}

countTrailingZerosBV :: KnownNat n => BitVector n -> I.Index (n+1)
countTrailingZerosBV = V.foldl (\l r -> if eq## r low then 1 + l else 0) 0 . V.bv2v
{-# INLINE countTrailingZerosBV #-}

{-# NOINLINE reduceAnd# #-}
reduceAnd# :: KnownNat n => BitVector n -> Bit
reduceAnd# bv@(BV 0 i) = Bit 0 (smallInteger (dataToTag# check))
  where
    check = i == maxI

    sz    = natVal bv
    maxI  = (2 ^ sz) - 1
reduceAnd# bv = V.foldl (.&.) 1 (V.bv2v bv)

{-# NOINLINE reduceOr# #-}
reduceOr# :: KnownNat n => BitVector n -> Bit
reduceOr# (BV 0 i) = Bit 0 (smallInteger (dataToTag# check))
  where
    check = i /= 0
reduceOr# bv = V.foldl (.|.) 0 (V.bv2v bv)

{-# NOINLINE reduceXor# #-}
reduceXor# :: KnownNat n => BitVector n -> Bit
reduceXor# (BV 0 i) = Bit 0 (toInteger (popCount i `mod` 2))
reduceXor# bv = undefErrorU "reduceXor" bv

instance Default (BitVector n) where
  def = minBound#

-- * Accessors
-- ** Length information
{-# NOINLINE size# #-}
size# :: KnownNat n => BitVector n -> Int
size# bv = fromInteger (natVal bv)

{-# NOINLINE maxIndex# #-}
maxIndex# :: KnownNat n => BitVector n -> Int
maxIndex# bv = fromInteger (natVal bv) - 1

-- ** Indexing
{-# NOINLINE index# #-}
index# :: KnownNat n => BitVector n -> Int -> Bit
index# bv@(BV m v) i
    | i >= 0 && i < sz = Bit (smallInteger (dataToTag# (testBit m i)))
                             (smallInteger (dataToTag# (testBit v i)))
    | otherwise        = err
  where
    sz  = fromInteger (natVal bv)
    err = error $ concat [ "(!): "
                         , show i
                         , " is out of range ["
                         , show (sz - 1)
                         , "..0]"
                         ]

{-# NOINLINE msb# #-}
-- | MSB
msb# :: forall n . KnownNat n => BitVector n -> Bit
msb# (BV m v)
  = let i = fromInteger (natVal (Proxy @n) - 1)
    in  Bit (smallInteger (dataToTag# (testBit m i)))
            (smallInteger (dataToTag# (testBit v i)))

{-# NOINLINE lsb# #-}
-- | LSB
lsb# :: BitVector n -> Bit
lsb# (BV m v) = Bit (smallInteger (dataToTag# (testBit m 0)))
                    (smallInteger (dataToTag# (testBit v 0)))

{-# NOINLINE slice# #-}
slice# :: BitVector (m + 1 + i) -> SNat m -> SNat n -> BitVector (m + 1 - n)
slice# (BV msk i) m n = BV (shiftR (msk .&. mask) n')
                           (shiftR (i   .&. mask) n')
  where
    m' = snatToInteger m
    n' = snatToNum n

    mask = 2 ^ (m' + 1) - 1

-- * Constructions

-- ** Concatenation
{-# NOINLINE (++#) #-}
-- | Concatenate two 'BitVector's
(++#) :: KnownNat m => BitVector n -> BitVector m -> BitVector (n + m)
(BV m1 v1) ++# bv2@(BV m2 v2) = BV (m1' .|. m2) (v1' .|. v2)
  where
    size2 = fromInteger (natVal bv2)
    v1' = shiftL v1 size2
    m1' = shiftL m1 size2

-- * Modifying BitVectors
{-# NOINLINE replaceBit# #-}
replaceBit# :: KnownNat n => BitVector n -> Int -> Bit -> BitVector n
replaceBit# bv@(BV m v) i (Bit mb b)
    | i >= 0 && i < sz = BV (clearBit m i  .|. (mb `shiftL` i))
                            (if b == 1 && mb == 0 then setBit v i else clearBit v i)
    | otherwise        = err
  where
    sz   = fromInteger (natVal bv)
    err  = error $ concat [ "replaceBit: "
                          , show i
                          , " is out of range ["
                          , show (sz - 1)
                          , "..0]"
                          ]

{-# NOINLINE setSlice# #-}
setSlice# :: BitVector (m + 1 + i) -> SNat m -> SNat n -> BitVector (m + 1 - n)
          -> BitVector (m + 1 + i)
setSlice# (BV iMask i) m n (BV jMask j) = BV ((iMask .&. mask) .|. jMask')
                                             ((i     .&. mask) .|. j')
  where
    m' = snatToInteger m
    n' = snatToInteger n

    j'     = shiftL j     (fromInteger n')
    jMask' = shiftL jMask (fromInteger n')
    mask = complement ((2 ^ (m' + 1) - 1) `xor` (2 ^ n' - 1))

{-# NOINLINE split# #-}
split# :: forall n m . KnownNat n
       => BitVector (m + n) -> (BitVector m, BitVector n)
split# (BV m i) = (BV lMask l, BV rMask r)
  where
    n     = fromInteger (natVal (Proxy @n))
    mask  = 1 `shiftL` n
    -- The code below is faster than:
    -- > (l,r) = i `divMod` mask
    r     = i `mod` mask
    rMask = m `mod` mask
    l     = i `shiftR` n
    lMask = m `shiftR` n


and#, or#, xor# :: BitVector n -> BitVector n -> BitVector n
{-# NOINLINE and# #-}
and# (BV m1 v1) (BV m2 v2) = BV mask (v1 .&. v2  .&. complement mask)
  where
    mask = (m1.&.v2 .|. m1.&.m2 .|. m2.&.v1)

{-# NOINLINE or# #-}
or# (BV m1 v1) (BV m2 v2) = BV mask ((v1.|.v2) .&. complement mask)
  where
    mask = m1 .&. complement v2  .|.  m1.&.m2  .|.  m2 .&. complement v1

{-# NOINLINE xor# #-}
xor# (BV m1 v1) (BV m2 v2) = BV mask ((v1 `xor` v2) .&. complement mask)
  where
    mask = m1 .|. m2


{-# NOINLINE complement# #-}
complement# :: KnownNat n => BitVector n -> BitVector n
complement# (BV m v) = fromInteger_INLINE m (complement v .&. complement m)

shiftL#, shiftR#, rotateL#, rotateR#
  :: KnownNat n => BitVector n -> Int -> BitVector n

{-# NOINLINE shiftL# #-}
shiftL# (BV m v) i
  | i < 0     = error
              $ "'shiftL undefined for negative number: " ++ show i
  | otherwise = fromInteger_INLINE (shiftL m i) (shiftL v i)

{-# NOINLINE shiftR# #-}
shiftR# (BV m v) i
  | i < 0     = error
              $ "'shiftR undefined for negative number: " ++ show i
  | otherwise = BV (shiftR m i) (shiftR v i)

{-# NOINLINE rotateL# #-}
rotateL# _ b | b < 0   = error "'shiftL undefined for negative numbers"
rotateL# bv@(BV m v) b = fromInteger_INLINE (ml .|. mr) (vl .|. vr)
  where
    vl    = shiftL v b'
    vr    = shiftR v b''

    ml    = shiftL m b'
    mr    = shiftR m b''

    b'   = b `mod` sz
    b''  = sz - b'
    sz   = fromInteger (natVal bv)

{-# NOINLINE rotateR# #-}
rotateR# _ b | b < 0   = error "'shiftR undefined for negative numbers"
rotateR# bv@(BV m v) b = fromInteger_INLINE (ml .|. mr) (vl .|. vr)
  where
    vl   = shiftR v b'
    vr   = shiftL v b''
    ml   = shiftR m b'
    mr   = shiftL m b''

    b'  = b `mod` sz
    b'' = sz - b'
    sz  = fromInteger (natVal bv)

popCountBV :: forall n . KnownNat n => BitVector (n+1) -> I.Index (n+2)
popCountBV bv =
  let v = V.bv2v bv
  in  sum (V.map (fromIntegral . pack#) v)
{-# INLINE popCountBV #-}

instance Resize BitVector where
  resize     = resize#
  zeroExtend = extend
  signExtend = \bv -> (if msb# bv == low then id else complement) 0 ++# bv
  truncateB  = resize#

{-# NOINLINE resize# #-}
resize# :: forall n m . KnownNat m => BitVector n -> BitVector m
resize# (BV msk i) =
  let m = 1 `shiftL` fromInteger (natVal (Proxy @m))
  in  if i >= m then fromInteger_INLINE msk i else BV msk i

instance KnownNat n => Lift (BitVector n) where
  lift bv@(BV m i) = sigE [| fromInteger# m i |] (decBitVector (natVal bv))
  {-# NOINLINE lift #-}

decBitVector :: Integer -> TypeQ
decBitVector n = appT (conT ''BitVector) (litT $ numTyLit n)

instance KnownNat n => SaturatingNum (BitVector n) where
  satAdd SatWrap a b = a +# b
  satAdd SatZero a b =
    let r = plus# a b
    in  if msb# r == low
           then resize# r
           else minBound#
  satAdd _ a b =
    let r  = plus# a b
    in  if msb# r == low
           then resize# r
           else maxBound#

  satSub SatWrap a b = a -# b
  satSub _ a b =
    let r = minus# a b
    in  if msb# r == low
           then resize# r
           else minBound#

  satMul SatWrap a b = a *# b
  satMul SatZero a b =
    let r       = times# a b
        (rL,rR) = split# r
    in  case rL of
          0 -> rR
          _ -> minBound#
  satMul _ a b =
    let r       = times# a b
        (rL,rR) = split# r
    in  case rL of
          0 -> rR
          _ -> maxBound#

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


-- error for infix operator
undefErrorI :: (HasCallStack, KnownNat m, KnownNat n) => String -> BitVector m -> BitVector n -> a
undefErrorI op bv1 bv2 = withFrozenCallStack $
  errorX $ "Clash.Sized.BitVector." ++ op
  ++ " called with (partially) undefined arguments: "
  ++ show bv1 ++ " " ++ op ++" " ++ show bv2

-- error for prefix operator/function
undefErrorP :: (HasCallStack, KnownNat m, KnownNat n) => String -> BitVector m -> BitVector n -> a
undefErrorP op bv1 bv2 = withFrozenCallStack $
  errorX $ "Clash.Sized.BitVector." ++ op
  ++ " called with (partially) undefined arguments: "
  ++ show bv1 ++ " " ++ show bv2

-- error for prefix operator/function
undefErrorP3 :: (HasCallStack, KnownNat m, KnownNat n, KnownNat o) => String -> BitVector m -> BitVector n -> BitVector o -> a
undefErrorP3 op bv1 bv2 bv3 = withFrozenCallStack $
  errorX $ "Clash.Sized.BitVector." ++ op
  ++ " called with (partially) undefined arguments: "
  ++ show bv1 ++ " " ++ show bv2 ++ " " ++ show bv3

-- error for unary operator/function
undefErrorU :: (HasCallStack, KnownNat n) => String -> BitVector n -> a
-- undefErrorU op bv1 = undefError ("Clash.Sized.BitVector." ++ op) [bv1]
undefErrorU op bv1 = withFrozenCallStack $
  errorX $ "Clash.Sized.BitVector." ++ op
  ++ " called with (partially) undefined argument: "
  ++ show bv1

undefError :: (HasCallStack, KnownNat n) => String -> [BitVector n] -> a
undefError op bvs = withFrozenCallStack $
  errorX $ op
  ++ " called with (partially) undefined arguments: "
  ++ unwords (L.map show bvs)


-- | Implement BitVector undefinedness checking for unpack funtions
checkUnpackUndef :: (KnownNat n, Typeable a)
                 => (BitVector n -> a) -- ^ unpack function
                 -> BitVector n -> a
checkUnpackUndef f bv@(BV 0 _) = f bv
checkUnpackUndef _ bv = res
  where
    ty = typeOf res
    res = undefError (show ty ++ ".unpack") [bv]
{-# NOINLINE checkUnpackUndef #-}

-- | Create a BitVector with all its bits undefined
undefined# :: forall n . KnownNat n => BitVector n
undefined# =
  let m = 1 `shiftL` fromInteger (natVal (Proxy @n))
  in  BV (m-1) 0
{-# NOINLINE undefined# #-}

-- | Check if one BitVector is like another.
-- Undefined bits in the second argument are interpreted as don't care bits.
--
-- >>> let expected = $$(bLit "1.") :: BitVector 2
-- >>> let checked  = $$(bLit "11") :: BitVector 2
-- >>> checked  `isLike` expected
-- True
-- >>> expected `isLike` checked
-- False
--
-- __NB__: Not synthesisable
isLike :: BitVector n -> BitVector n -> Bool
isLike (BV cMask c) (BV eMask e) = e' == c' && e' == c''
  where
    -- | set don't care bits to 0
    e' = e .&. complement eMask

    -- | checked with undefined bits set to 0
    c' = (c .&. complement cMask) .&. complement eMask
    -- | checked with undefined bits set to 1
    c'' = (c .|. cMask) .&. complement eMask
{-# NOINLINE isLike #-}
