{-|
Copyright  :  (C) 2013-2016, University of Twente,
                  2016     , Myrtle Software Ltd
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MagicHash             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
#if __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE NoStarIsType #-}
#endif

{-# LANGUAGE Unsafe #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

{-# OPTIONS_HADDOCK show-extensions not-home #-}

module Clash.Sized.Internal.Index
  ( -- * Datatypes
    Index (..)
    -- * Construction
  , fromSNat
    -- * Type classes
    -- ** BitPack
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
  , maxBound#
    -- ** Num
  , (+#)
  , (-#)
  , (*#)
  , fromInteger#
    -- ** ExtendingNum
  , plus#
  , minus#
  , times#
    -- ** Integral
  , quot#
  , rem#
  , toInteger#
    -- ** Resize
  , resize#
  )
where

import Control.DeepSeq            (NFData (..))
import Data.Data                  (Data)
import Data.Default.Class         (Default (..))
import Data.Proxy                 (Proxy (..))
import Text.Read                  (Read (..), ReadPrec)
import Language.Haskell.TH        (TypeQ, appT, conT, litT, numTyLit, sigE)
import Language.Haskell.TH.Syntax (Lift(..))
import Numeric.Natural            (Natural)
import GHC.TypeLits               (CmpNat, KnownNat, Nat, type (+), type (-),
                                   type (*), type (<=), natVal)
import GHC.TypeLits.Extra         (CLog)
import Test.QuickCheck.Arbitrary  (Arbitrary (..), CoArbitrary (..),
                                   arbitraryBoundedIntegral,
                                   coarbitraryIntegral, shrinkIntegral)

import Clash.Class.BitPack        (BitPack (..))
import Clash.Class.Num            (ExtendingNum (..), SaturatingNum (..),
                                   SaturationMode (..))
import Clash.Class.Resize         (Resize (..))
import {-# SOURCE #-} Clash.Sized.Internal.BitVector (BitVector (BV),undefError)
import Clash.Promoted.Nat         (SNat, snatToNum, leToPlusKN)
import Clash.XException           (ShowX (..), Undefined, showsPrecXWith)

-- | Arbitrary-bounded unsigned integer represented by @ceil(log_2(n))@ bits.
--
-- Given an upper bound @n@, an 'Index' @n@ number has a range of: [0 .. @n@-1]
--
-- >>> maxBound :: Index 8
-- 7
-- >>> minBound :: Index 8
-- 0
-- >>> read (show (maxBound :: Index 8)) :: Index 8
-- 7
-- >>> 1 + 2 :: Index 8
-- 3
-- >>> 2 + 6 :: Index 8
-- *** Exception: Clash.Sized.Index: result 8 is out of bounds: [0..7]
-- ...
-- >>> 1 - 3 :: Index 8
-- *** Exception: Clash.Sized.Index: result -2 is out of bounds: [0..7]
-- ...
-- >>> 2 * 3 :: Index 8
-- 6
-- >>> 2 * 4 :: Index 8
-- *** Exception: Clash.Sized.Index: result 8 is out of bounds: [0..7]
-- ...
newtype Index (n :: Nat) =
    -- | The constructor, 'I', and the field, 'unsafeToInteger', are not
    -- synthesisable.
    I { unsafeToInteger :: Integer }
  deriving (Data,Undefined)

instance NFData (Index n) where
  rnf (I i) = rnf i `seq` ()
  {-# NOINLINE rnf #-}
  -- NOINLINE is needed so that Clash doesn't trip on the "Index ~# Integer"
  -- coercion

instance (KnownNat n, 1 <= n) => BitPack (Index n) where
  type BitSize (Index n) = CLog 2 n
  pack   = pack#
  unpack = unpack#

-- | Safely convert an `SNat` value to an `Index`
fromSNat :: (KnownNat m, CmpNat n m ~ 'LT) => SNat n -> Index m
fromSNat = snatToNum

{-# NOINLINE pack# #-}
pack# :: Index n -> BitVector (CLog 2 n)
pack# (I i) = BV 0 i

{-# NOINLINE unpack# #-}
unpack# :: (KnownNat n, 1 <= n) => BitVector (CLog 2 n) -> Index n
unpack# (BV 0 i) = fromInteger_INLINE i
unpack# bv = undefError "Index.unpack" [bv]

instance Eq (Index n) where
  (==) = eq#
  (/=) = neq#

{-# NOINLINE eq# #-}
eq# :: (Index n) -> (Index n) -> Bool
(I n) `eq#` (I m) = n == m

{-# NOINLINE neq# #-}
neq# :: (Index n) -> (Index n) -> Bool
(I n) `neq#` (I m) = n /= m

instance Ord (Index n) where
  (<)  = lt#
  (>=) = ge#
  (>)  = gt#
  (<=) = le#

lt#,ge#,gt#,le# :: Index n -> Index n -> Bool
{-# NOINLINE lt# #-}
lt# (I n) (I m) = n < m
{-# NOINLINE ge# #-}
ge# (I n) (I m) = n >= m
{-# NOINLINE gt# #-}
gt# (I n) (I m) = n > m
{-# NOINLINE le# #-}
le# (I n) (I m) = n <= m

-- | The functions: 'enumFrom', 'enumFromThen', 'enumFromTo', and
-- 'enumFromThenTo', are not synthesisable.
instance KnownNat n => Enum (Index n) where
  succ           = (+# fromInteger# 1)
  pred           = (-# fromInteger# 1)
  toEnum         = fromInteger# . toInteger
  fromEnum       = fromEnum . toInteger#
  enumFrom       = enumFrom#
  enumFromThen   = enumFromThen#
  enumFromTo     = enumFromTo#
  enumFromThenTo = enumFromThenTo#

{-# NOINLINE enumFrom# #-}
{-# NOINLINE enumFromThen# #-}
{-# NOINLINE enumFromTo# #-}
{-# NOINLINE enumFromThenTo# #-}
enumFrom#       :: KnownNat n => Index n -> [Index n]
enumFromThen#   :: KnownNat n => Index n -> Index n -> [Index n]
enumFromTo#     :: Index n -> Index n -> [Index n]
enumFromThenTo# :: Index n -> Index n -> Index n -> [Index n]
enumFrom# x             = map fromInteger_INLINE [unsafeToInteger x ..]
enumFromThen# x y       = map fromInteger_INLINE [unsafeToInteger x, unsafeToInteger y ..]
enumFromTo# x y         = map I [unsafeToInteger x .. unsafeToInteger y]
enumFromThenTo# x1 x2 y = map I [unsafeToInteger x1, unsafeToInteger x2 .. unsafeToInteger y]

instance KnownNat n => Bounded (Index n) where
  minBound = fromInteger# 0
  maxBound = maxBound#

{-# NOINLINE maxBound# #-}
maxBound# :: KnownNat n => Index n
maxBound# = let res = fromInteger_INLINE (natVal res - 1) in res

-- | Operators report an error on overflow and underflow
instance KnownNat n => Num (Index n) where
  (+)         = (+#)
  (-)         = (-#)
  (*)         = (*#)
  negate      = (maxBound# -#)
  abs         = id
  signum i    = if i == 0 then 0 else 1
  fromInteger = fromInteger#

(+#),(-#),(*#) :: KnownNat n => Index n -> Index n -> Index n
{-# NOINLINE (+#) #-}
(+#) (I a) (I b) = fromInteger_INLINE $ a + b

{-# NOINLINE (-#) #-}
(-#) (I a) (I b) = fromInteger_INLINE $ a - b

{-# NOINLINE (*#) #-}
(*#) (I a) (I b) = fromInteger_INLINE $ a * b

fromInteger# :: KnownNat n => Integer -> Index n
{-# NOINLINE fromInteger# #-}
fromInteger# = fromInteger_INLINE
{-# INLINE fromInteger_INLINE #-}
fromInteger_INLINE :: forall n . KnownNat n => Integer -> Index n
fromInteger_INLINE i = bound `seq` if i > (-1) && i < bound then I i else err
  where
    bound = natVal (Proxy @n)
    err   = error ("Clash.Sized.Index: result " ++ show i ++
                   " is out of bounds: [0.." ++ show (bound - 1) ++ "]")

instance ExtendingNum (Index m) (Index n) where
  type AResult (Index m) (Index n) = Index (m + n - 1)
  add  = plus#
  sub = minus#
  type MResult (Index m) (Index n) = Index (((m - 1) * (n - 1)) + 1)
  mul = times#

plus#, minus# :: Index m -> Index n -> Index (m + n - 1)
{-# NOINLINE plus# #-}
plus# (I a) (I b) = I (a + b)

{-# NOINLINE minus# #-}
minus# (I a) (I b) =
  let z   = a - b
      err = error ("Clash.Sized.Index.minus: result " ++ show z ++
                   " is smaller than 0")
      res = if z < 0 then err else I z
  in  res

{-# NOINLINE times# #-}
times# :: Index m -> Index n -> Index (((m - 1) * (n - 1)) + 1)
times# (I a) (I b) = I (a * b)

instance (KnownNat n, 1 <= n) => SaturatingNum (Index n) where
  satAdd SatWrap a b =
    leToPlusKN @1 a $ \a' ->
    leToPlusKN @1 b $ \b' ->
      case plus# a' b' of
        z | let m = fromInteger# (natVal (Proxy @ n))
          , z >= m -> resize# (z - m)
        z -> resize# z
  satAdd SatZero a b =
    leToPlusKN @1 a $ \a' ->
    leToPlusKN @1 b $ \b' ->
      case plus# a' b' of
        z | let m = fromInteger# (natVal (Proxy @ n))
          , z >= m -> fromInteger# 0
        z -> resize# z
  satAdd _ a b =
    leToPlusKN @1 a $ \a' ->
    leToPlusKN @1 b $ \b' ->
      case plus# a' b' of
        z | let m = fromInteger# (natVal (Proxy @ n))
          , z >= m -> maxBound#
        z -> resize# z

  satSub SatWrap a b =
    if lt# a b
       then maxBound -# (b -# a) +# 1
       else a -# b

  satSub _ a b =
    if lt# a b
       then fromInteger# 0
       else a -# b

  satMul SatWrap a b =
    leToPlusKN @1 a $ \a' ->
    leToPlusKN @1 b $ \b' ->
      case times# a' b' of
        z | let m = fromInteger# (natVal (Proxy @ n))
          , z >= m -> resize# (z - m)
        z -> resize# z
  satMul SatZero a b =
    leToPlusKN @1 a $ \a' ->
    leToPlusKN @1 b $ \b' ->
      case times# a' b' of
        z | let m = fromInteger# (natVal (Proxy @ n))
          , z >= m -> fromInteger# 0
        z -> resize# z
  satMul _ a b =
    leToPlusKN @1 a $ \a' ->
    leToPlusKN @1 b $ \b' ->
      case times# a' b' of
        z | let m = fromInteger# (natVal (Proxy @ n))
          , z >= m -> maxBound#
        z -> resize# z

instance KnownNat n => Real (Index n) where
  toRational = toRational . toInteger#

instance KnownNat n => Integral (Index n) where
  quot        = quot#
  rem         = rem#
  div         = quot#
  mod         = rem#
  quotRem n d = (n `quot#` d,n `rem#` d)
  divMod  n d = (n `quot#` d,n `rem#` d)
  toInteger   = toInteger#

quot#,rem# :: Index n -> Index n -> Index n
{-# NOINLINE quot# #-}
(I a) `quot#` (I b) = I (a `div` b)
{-# NOINLINE rem# #-}
(I a) `rem#` (I b) = I (a `rem` b)

{-# NOINLINE toInteger# #-}
toInteger# :: Index n -> Integer
toInteger# (I n) = n

instance Resize Index where
  resize     = resize#
  zeroExtend = extend
  truncateB  = resize#

resize# :: KnownNat m => Index n -> Index m
resize# (I i) = fromInteger_INLINE i
{-# NOINLINE resize# #-}

instance KnownNat n => Lift (Index n) where
  lift u@(I i) = sigE [| fromInteger# i |] (decIndex (natVal u))
  {-# NOINLINE lift #-}

decIndex :: Integer -> TypeQ
decIndex n = appT (conT ''Index) (litT $ numTyLit n)

instance Show (Index n) where
  show (I i) = show i
  {-# NOINLINE show #-}

instance ShowX (Index n) where
  showsPrecX = showsPrecXWith showsPrec

-- | None of the 'Read' class' methods are synthesisable.
instance KnownNat n => Read (Index n) where
  readPrec = fromIntegral <$> (readPrec :: ReadPrec Natural)

instance KnownNat n => Default (Index n) where
  def = fromInteger# 0

instance KnownNat n => Arbitrary (Index n) where
  arbitrary = arbitraryBoundedIntegral
  shrink    = shrinkIndex

shrinkIndex :: KnownNat n => Index n -> [Index n]
shrinkIndex x | natVal x < 3 = case toInteger x of
                                 1 -> [0]
                                 _ -> []
              -- 'shrinkIntegral' uses "`quot` 2", which for 'Index' types with
              -- an upper bound less than 2 results in an error.
              | otherwise    = shrinkIntegral x

instance KnownNat n => CoArbitrary (Index n) where
  coarbitrary = coarbitraryIntegral
