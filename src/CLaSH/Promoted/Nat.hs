{-|
Copyright  :  (C) 2013-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

{-# LANGUAGE Trustworthy #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_HADDOCK show-extensions #-}

module CLaSH.Promoted.Nat
  ( -- * Singleton natural numbers
    -- ** Data type
    SNat (..)
    -- ** Construction
  , snatProxy
  , withSNat
    -- ** Conversion
  , snatToInteger
    -- ** Arithmetic
  , addSNat, subSNat, mulSNat, powSNat
    -- * Unary/Peano-encoded natural numbers
    -- ** Data type
  , UNat (..)
    -- ** Construction
  , toUNat
    -- ** Arithmetic
  , addUNat, mulUNat, powUNat
    -- * Base-2 encoded natural numbers
    -- ** Data type
  , BNat (..)
    -- ** Construction
  , toBNat
    -- ** Showing base-2 encoded natural numbers
  , showBNat
    -- ** Arithmetic
  , succBNat, predBNat, addBNat, mulBNat, powBNat, div2BNat, div2Sub1BNat
    -- ** Normalisation
  , stripZeros
  )
where

import Data.Reflection (reifyNat)
import GHC.TypeLits    (KnownNat, Nat, type (+), type (-), type (*), type (^),
                        natVal)
import Unsafe.Coerce   (unsafeCoerce)

-- | Singleton value for a type-level natural number 'n'
--
-- * "CLaSH.Promoted.Nat.Literals" contains a list of predefined 'SNat' literals
-- * "CLaSH.Promoted.Nat.TH" has functions to easily create large ranges of new
--   'SNat' literals
data SNat (n :: Nat) where
  SNat :: KnownNat n => SNat n

-- | Create an @`SNat` n@ from a proxy for /n/
snatProxy :: KnownNat n => proxy n -> SNat n
snatProxy _ = SNat

instance Show (SNat n) where
  show p@SNat = 'd' : show (natVal p)

{-# INLINE withSNat #-}
-- | Supply a function with a singleton natural 'n' according to the context
withSNat :: KnownNat n => (SNat n -> a) -> a
withSNat f = f SNat

{-# INLINE snatToInteger #-}
-- | Reify the type-level 'Nat' @n@ to it's term-level 'Integer' representation.
snatToInteger :: SNat n -> Integer
snatToInteger p@SNat = natVal p

-- | Unary representation of a type-level natural
--
-- __NB__: Not synthesisable
data UNat :: Nat -> * where
  UZero :: UNat 0
  USucc :: UNat n -> UNat (n + 1)

instance KnownNat n => Show (UNat n) where
  show x = 'u':show (natVal x)

-- | Convert a singleton natural number to its unary representation
--
-- __NB__: Not synthesisable
toUNat :: SNat n -> UNat n
toUNat p@SNat = fromI (natVal p)
  where
    fromI :: Integer -> UNat m
    fromI 0 = unsafeCoerce UZero
    fromI n = unsafeCoerce (USucc (fromI (n - 1)))

-- | Add two unary singleton natural numbers
--
-- __NB__: Not synthesisable
addUNat :: UNat n -> UNat m -> UNat (n + m)
addUNat UZero     y     = y
addUNat x         UZero = x
addUNat (USucc x) y     = USucc (addUNat x y)

-- | Multiply two unary singleton natural numbers
--
-- __NB__: Not synthesisable
mulUNat :: UNat n -> UNat m -> UNat (n * m)
mulUNat UZero      _     = UZero
mulUNat _          UZero = UZero
mulUNat (USucc x) y      = addUNat y (mulUNat x y)

-- | Power of two unary singleton natural numbers
--
-- __NB__: Not synthesisable
powUNat :: UNat n -> UNat m -> UNat (n ^ m)
powUNat _ UZero     = USucc UZero
powUNat x (USucc y) = mulUNat x (powUNat x y)

-- | Add two singleton natural numbers
addSNat :: SNat a -> SNat b -> SNat (a+b)
addSNat x y = reifyNat (snatToInteger x + snatToInteger y)
            $ \p -> unsafeCoerce (snatProxy p)
{-# NOINLINE addSNat #-}

-- | Subtract two singleton natural numbers
subSNat :: SNat a -> SNat b -> SNat (a-b)
subSNat x y = reifyNat (snatToInteger x - snatToInteger y)
            $ \p -> unsafeCoerce (snatProxy p)
{-# NOINLINE subSNat #-}

-- | Multiply two singleton natural numbers
mulSNat :: SNat a -> SNat b -> SNat (a*b)
mulSNat x y = reifyNat (snatToInteger x * snatToInteger y)
            $ \p -> unsafeCoerce (snatProxy p)
{-# NOINLINE mulSNat #-}

-- | Power of two singleton natural numbers
powSNat :: SNat a -> SNat b -> SNat (a^b)
powSNat x y = reifyNat (snatToInteger x ^ snatToInteger y)
            $ \p -> unsafeCoerce (snatProxy p)
{-# NOINLINE powSNat #-}

-- | Base-2 encoded natural number
--
-- __NB__: LSB is the left-most constructor:
--
-- >>> B0 (B1 (B1 BT))
-- b6
--
-- == Constructors
--
-- * Starting/Terminating element:
--
--      @
--      __BT__ :: 'BNat' 0
--      @
--
-- * Append a zero (/0/):
--
--      @
--      __B0__ :: 'BNat' n -> 'BNat' (2 '*' n)
--      @
--
-- * Append a one (/1/):
--
--      @
--      __B1__ :: 'BNat' n -> 'BNat' ((2 '*' n) '+' 1)
--      @
data BNat :: Nat -> * where
  BT :: BNat 0
  B0 :: BNat n -> BNat (2*n)
  B1 :: BNat n -> BNat ((2*n) + 1)

instance KnownNat n => Show (BNat n) where
  show x = 'b':show (natVal x)

-- | Show a base-2 encoded natural as a binary literal
--
-- __NB__: LSB is shown as the right-most bit
showBNat :: BNat n -> String
showBNat = go []
  where
    go :: String -> BNat m -> String
    go xs BT  = "0b" ++ xs
    go xs (B0 x) = go ('0':xs) x
    go xs (B1 x) = go ('1':xs) x

-- | Convert a singleton natural number to its base-2 representation
--
-- __NB__: Not synthesisable
toBNat :: SNat n -> BNat n
toBNat s@SNat = toBNat' (natVal s)
  where
    toBNat' :: Integer -> BNat m
    toBNat' 0 = unsafeCoerce BT
    toBNat' n = case n `divMod` 2 of
      (n',1) -> unsafeCoerce (B1 (toBNat' n'))
      (n',_) -> unsafeCoerce (B0 (toBNat' n'))

-- | Add two base-2 encoded natural numbers
addBNat :: BNat n -> BNat m -> BNat (n+m)
addBNat (B0 a) (B0 b) = B0 (addBNat a b)
addBNat (B0 a) (B1 b) = B1 (addBNat a b)
addBNat (B1 a) (B0 b) = B1 (addBNat a b)
addBNat (B1 a) (B1 b) = B0 (succBNat (addBNat a b))
addBNat BT     b      = b
addBNat a      BT     = a

-- | Multiply two base-2 encoded natural numbers
mulBNat :: BNat n -> BNat m -> BNat (n*m)
mulBNat BT      _  = BT
mulBNat _       BT = BT
mulBNat (B0 a)  b  = B0 (mulBNat a b)
mulBNat (B1 a)  b  = addBNat (B0 (mulBNat a b)) b

-- | Power of two base-2 encoded natural numbers
powBNat :: BNat n -> BNat m -> BNat (n^m)
powBNat _  BT      = B1 BT
powBNat a  (B0 b)  = let z = powBNat a b
                     in  mulBNat z z
powBNat a  (B1 b)  = let z = powBNat a b
                     in  mulBNat a (mulBNat z z)

-- | Successor of a base-2 encoded natural number
succBNat :: BNat n -> BNat (n+1)
succBNat BT     = B1 BT
succBNat (B0 a) = B1 a
succBNat (B1 a) = B0 (succBNat a)

-- | Predecessor of a base-2 encoded natural number
predBNat :: BNat n -> BNat (n - 1)
predBNat (B1 a) = B0 a
predBNat (B0 a) = B1 (predBNat a)
predBNat BT     = error "impossible"

-- | Divide a base-2 encoded natural number by 2
div2BNat :: BNat (2*n) -> BNat n
div2BNat (B0 x) = x
div2BNat BT     = BT
div2BNat (B1 _) = error "impossible"

-- | Subtract 1 and divide a base-2 encoded natural number by 2
div2Sub1BNat :: BNat (2*n+1) -> BNat n
div2Sub1BNat (B1 x) = x
div2Sub1BNat _      = error "impossible"

-- | Strip non-contributing zero's from a base-2 encoded natural number
--
-- >>> B1 (B0 (B0 (B0 BT)))
-- b1
-- >>> showBNat (B1 (B0 (B0 (B0 BT))))
-- "0b0001"
-- >>> showBNat (stripZeros (B1 (B0 (B0 (B0 BT)))))
-- "0b1"
-- >>> stripZeros (B1 (B0 (B0 (B0 BT))))
-- b1
stripZeros :: BNat n -> BNat n
stripZeros BT      = BT
stripZeros (B1 x)  = B1 (stripZeros x)
stripZeros (B0 BT) = BT
stripZeros (B0 x)  = case stripZeros x of
  BT -> BT
  k  -> B0 k
