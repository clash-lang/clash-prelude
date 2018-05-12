{-|
Copyright  :  (C) 2013-2016, University of Twente,
                  2016     , Myrtle Software Ltd
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE RankNTypes          #-}

{-# LANGUAGE Trustworthy #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module Clash.Promoted.Nat
  ( -- * Singleton natural numbers
    -- ** Data type
    SNat (..)
    -- ** Construction
  , snatProxy
  , withSNat
    -- ** Conversion
  , snatToInteger, snatToNum
    -- ** Arithmetic
  , addSNat, mulSNat, powSNat
    -- *** Partial
  , subSNat, divSNat, modSNat, flogBaseSNat, clogBaseSNat, logBaseSNat
    -- *** Specialised
  , pow2SNat
    -- * Unary/Peano-encoded natural numbers
    -- ** Data type
  , UNat (..)
    -- ** Construction
  , toUNat
    -- ** Conversion
  , fromUNat
    -- ** Arithmetic
  , addUNat, mulUNat, powUNat
    -- *** Partial
  , predUNat, subUNat
    -- * Base-2 encoded natural numbers
    -- ** Data type
  , BNat (..)
    -- ** Construction
  , toBNat
    -- ** Conversion
  , fromBNat
    -- ** Pretty printing base-2 encoded natural numbers
  , showBNat
    -- ** Arithmetic
  , succBNat, addBNat, mulBNat, powBNat
    -- *** Partial
  , predBNat, div2BNat, div2Sub1BNat, log2BNat
    -- ** Normalisation
  , stripZeros
    -- * Constraints on natural numbers
  , leToPlus
  , leToPlusKN
  , plusToLe
  , plusToLeKN
  )
where

import GHC.TypeLits       (KnownNat, Nat, type (+), type (-), type (*),
                           type (^), type (<=), natVal)
import GHC.TypeLits.Extra (CLog, FLog, Div, Log, Mod)
import Language.Haskell.TH (appT, conT, litT, numTyLit, sigE)
import Language.Haskell.TH.Syntax (Lift (..))
import Unsafe.Coerce      (unsafeCoerce)
import Clash.XException   (ShowX (..), showsPrecXWith)

{- $setup
>>> :set -XBinaryLiterals
>>> import Clash.Promoted.Nat.Literals (d789)
-}

-- | Singleton value for a type-level natural number 'n'
--
-- * "Clash.Promoted.Nat.Literals" contains a list of predefined 'SNat' literals
-- * "Clash.Promoted.Nat.TH" has functions to easily create large ranges of new
--   'SNat' literals
data SNat (n :: Nat) where
  SNat :: KnownNat n => SNat n

instance Lift (SNat n) where
  lift s = sigE [| SNat |]
                (appT (conT ''SNat) (litT $ numTyLit (snatToInteger s)))

-- | Create an @`SNat` n@ from a proxy for /n/
snatProxy :: KnownNat n => proxy n -> SNat n
snatProxy _ = SNat

instance Show (SNat n) where
  show p@SNat = 'd' : show (natVal p)

instance ShowX (SNat n) where
  showsPrecX = showsPrecXWith showsPrec

{-# INLINE withSNat #-}
-- | Supply a function with a singleton natural 'n' according to the context
withSNat :: KnownNat n => (SNat n -> a) -> a
withSNat f = f SNat

{-# INLINE snatToInteger #-}
-- | Reify the type-level 'Nat' @n@ to it's term-level 'Integer' representation.
snatToInteger :: SNat n -> Integer
snatToInteger p@SNat = natVal p

-- | Reify the type-level 'Nat' @n@ to it's term-level 'Num'ber.
snatToNum :: Num a => SNat n -> a
snatToNum p@SNat = fromInteger (natVal p)
{-# INLINE snatToNum #-}

-- | Unary representation of a type-level natural
--
-- __NB__: Not synthesisable
data UNat :: Nat -> * where
  UZero :: UNat 0
  USucc :: UNat n -> UNat (n + 1)

instance KnownNat n => Show (UNat n) where
  show x = 'u':show (natVal x)

instance KnownNat n => ShowX (UNat n) where
  showsPrecX = showsPrecXWith showsPrec

-- | Convert a singleton natural number to its unary representation
--
-- __NB__: Not synthesisable
toUNat :: SNat n -> UNat n
toUNat p@SNat = fromI (natVal p)
  where
    fromI :: Integer -> UNat m
    fromI 0 = unsafeCoerce UZero
    fromI n = unsafeCoerce (USucc (fromI (n - 1)))

-- | Convert a unary-encoded natural number to its singleton representation
--
-- __NB__: Not synthesisable
fromUNat :: UNat n -> SNat n
fromUNat UZero     = SNat :: SNat 0
fromUNat (USucc x) = addSNat (fromUNat x) (SNat :: SNat 1)

-- | Add two unary-encoded natural numbers
--
-- __NB__: Not synthesisable
addUNat :: UNat n -> UNat m -> UNat (n + m)
addUNat UZero     y     = y
addUNat x         UZero = x
addUNat (USucc x) y     = USucc (addUNat x y)

-- | Multiply two unary-encoded natural numbers
--
-- __NB__: Not synthesisable
mulUNat :: UNat n -> UNat m -> UNat (n * m)
mulUNat UZero      _     = UZero
mulUNat _          UZero = UZero
mulUNat (USucc x) y      = addUNat y (mulUNat x y)

-- | Power of two unary-encoded natural numbers
--
-- __NB__: Not synthesisable
powUNat :: UNat n -> UNat m -> UNat (n ^ m)
powUNat _ UZero     = USucc UZero
powUNat x (USucc y) = mulUNat x (powUNat x y)

-- | Predecessor of a unary-encoded natural number
--
-- __NB__: Not synthesisable
predUNat :: UNat (n+1) -> UNat n
predUNat (USucc x) = x

-- | Subtract two unary-encoded natural numbers
--
-- __NB__: Not synthesisable
subUNat :: UNat (m+n) -> UNat n -> UNat m
subUNat x         UZero     = x
subUNat (USucc x) (USucc y) = subUNat x y
subUNat UZero     _         = error "impossible: 0 + (n + 1) ~ 0"

-- | Add two singleton natural numbers
addSNat :: SNat a -> SNat b -> SNat (a+b)
addSNat SNat SNat = SNat
{-# INLINE addSNat #-}
infixl 6 `addSNat`

-- | Subtract two singleton natural numbers
subSNat :: SNat (a+b) -> SNat b -> SNat a
subSNat SNat SNat = SNat
{-# INLINE subSNat #-}
infixl 6 `subSNat`

-- | Multiply two singleton natural numbers
mulSNat :: SNat a -> SNat b -> SNat (a*b)
mulSNat SNat SNat = SNat
{-# INLINE mulSNat #-}
infixl 7 `mulSNat`

-- | Power of two singleton natural numbers
powSNat :: SNat a -> SNat b -> SNat (a^b)
powSNat SNat SNat = SNat
{-# NOINLINE powSNat #-}
infixr 8 `powSNat`

-- | Division of two singleton natural numbers
divSNat :: (1 <= b) => SNat a -> SNat b -> SNat (Div a b)
divSNat SNat SNat = SNat
{-# INLINE divSNat #-}
infixl 7 `divSNat`

-- | Modulo of two singleton natural numbers
modSNat :: (1 <= b) => SNat a -> SNat b -> SNat (Mod a b)
modSNat SNat SNat = SNat
{-# INLINE modSNat #-}
infixl 7 `modSNat`

-- | Floor of the logarithm of a natural number
flogBaseSNat :: (2 <= base, 1 <= x)
             => SNat base -- ^ Base
             -> SNat x
             -> SNat (FLog base x)
flogBaseSNat SNat SNat = SNat
{-# NOINLINE flogBaseSNat #-}

-- | Ceiling of the logarithm of a natural number
clogBaseSNat :: (2 <= base, 1 <= x)
             => SNat base -- ^ Base
             -> SNat x
             -> SNat (CLog base x)
clogBaseSNat SNat SNat = SNat
{-# NOINLINE clogBaseSNat #-}

-- | Exact integer logarithm of a natural number
--
-- __NB__: Only works when the argument is a power of the base
logBaseSNat :: (FLog base x ~ CLog base x)
            => SNat base -- ^ Base
            -> SNat x
            -> SNat (Log base x)
logBaseSNat SNat SNat = SNat
{-# NOINLINE logBaseSNat #-}

-- | Power of two of a singleton natural number
pow2SNat :: SNat a -> SNat (2^a)
pow2SNat SNat = SNat
{-# INLINE pow2SNat #-}

-- | Base-2 encoded natural number
--
--    * __NB__: The LSB is the left/outer-most constructor:
--    * __NB__: Not synthesisable
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

instance KnownNat n => ShowX (BNat n) where
  showsPrecX = showsPrecXWith showsPrec

-- | Show a base-2 encoded natural as a binary literal
--
-- __NB__: The LSB is shown as the right-most bit
--
-- >>> d789
-- d789
-- >>> toBNat d789
-- b789
-- >>> showBNat (toBNat d789)
-- "0b1100010101"
-- >>> 0b1100010101 :: Integer
-- 789
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

-- | Convert a base-2 encoded natural number to its singleton representation
--
-- __NB__: Not synthesisable
fromBNat :: BNat n -> SNat n
fromBNat BT     = SNat :: SNat 0
fromBNat (B0 x) = mulSNat (SNat :: SNat 2) (fromBNat x)
fromBNat (B1 x) = addSNat (mulSNat (SNat :: SNat 2) (fromBNat x))
                          (SNat :: SNat 1)

-- | Add two base-2 encoded natural numbers
--
-- __NB__: Not synthesisable
addBNat :: BNat n -> BNat m -> BNat (n+m)
addBNat (B0 a) (B0 b) = B0 (addBNat a b)
addBNat (B0 a) (B1 b) = B1 (addBNat a b)
addBNat (B1 a) (B0 b) = B1 (addBNat a b)
addBNat (B1 a) (B1 b) = B0 (succBNat (addBNat a b))
addBNat BT     b      = b
addBNat a      BT     = a

-- | Multiply two base-2 encoded natural numbers
--
-- __NB__: Not synthesisable
mulBNat :: BNat n -> BNat m -> BNat (n*m)
mulBNat BT      _  = BT
mulBNat _       BT = BT
mulBNat (B0 a)  b  = B0 (mulBNat a b)
mulBNat (B1 a)  b  = addBNat (B0 (mulBNat a b)) b

-- | Power of two base-2 encoded natural numbers
--
-- __NB__: Not synthesisable
powBNat :: BNat n -> BNat m -> BNat (n^m)
powBNat _  BT      = B1 BT
powBNat a  (B0 b)  = let z = powBNat a b
                     in  mulBNat z z
powBNat a  (B1 b)  = let z = powBNat a b
                     in  mulBNat a (mulBNat z z)

-- | Successor of a base-2 encoded natural number
--
-- __NB__: Not synthesisable
succBNat :: BNat n -> BNat (n+1)
succBNat BT     = B1 BT
succBNat (B0 a) = B1 a
succBNat (B1 a) = B0 (succBNat a)

-- | Predecessor of a base-2 encoded natural number
--
-- __NB__: Not synthesisable
predBNat :: (1 <= n) => BNat n -> BNat (n-1)
predBNat (B1 a) = case stripZeros a of
  BT -> BT
  a' -> B0 a'
predBNat (B0 x) = B1 (predBNat x)

-- | Divide a base-2 encoded natural number by 2
--
-- __NB__: Not synthesisable
div2BNat :: BNat (2*n) -> BNat n
div2BNat BT     = BT
div2BNat (B0 x) = x
div2BNat (B1 _) = error "impossible: 2*n ~ 2*n+1"

-- | Subtract 1 and divide a base-2 encoded natural number by 2
--
-- __NB__: Not synthesisable
div2Sub1BNat :: BNat (2*n+1) -> BNat n
div2Sub1BNat (B1 x) = x
div2Sub1BNat _      = error "impossible: 2*n+1 ~ 2*n"

-- | Get the log2 of a base-2 encoded natural number
--
-- __NB__: Not synthesisable
log2BNat :: BNat (2^n) -> BNat n
log2BNat (B1 x) = case stripZeros x of
  BT -> BT
  _  -> error "impossible: 2^n ~ 2x+1"
log2BNat (B0 x) = succBNat (log2BNat x)

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
--
-- __NB__: Not synthesisable
stripZeros :: BNat n -> BNat n
stripZeros BT      = BT
stripZeros (B1 x)  = B1 (stripZeros x)
stripZeros (B0 BT) = BT
stripZeros (B0 x)  = case stripZeros x of
  BT -> BT
  k  -> B0 k

-- | Change a function that has an argument with an @(n + k)@ constraint to a
-- function with an argument that has an @(k <= n)@ constraint.
--
-- __NB__ It is the dual to 'plusToLe'
--
-- === __Examples__
--
-- Example 1
--
-- @
-- f :: Index (n+1) -> Index (n + 1) -> Bool
--
-- g :: (1 '<=' n) => Index n -> Index n -> Bool
-- g a b = 'leToPlus' \@1 $ \\a' -> 'leToPlus' \@1 $ \\b' -> f a' b'
-- @
--
-- Example 2
--
-- @
-- import Data.Bifunctor.Flip
--
-- head :: Vec (n + 1) a -> a
--
-- head' :: (1 '<=' n) => Vec n a -> a
-- head' a = 'leToPlus' \@1 (Flip a) (head . runFlip)
-- @
leToPlus
  :: forall (k :: Nat) (n :: Nat) f r
   . (k <= n)
  => f n
  -- ^ Argument with the @(k <= n)@ constraint
  -> (forall m . f (m + k) -> r)
  -- ^ Function with the @(n + k)@ constraint
  -> r
leToPlus a f = f @ (n-k) a
{-# INLINE leToPlus #-}

-- | Same as 'leToPlus' with added 'KnownNat' constraints
leToPlusKN
  :: forall (k :: Nat) (n :: Nat) f r
   . (k <= n, KnownNat n, KnownNat k)
  => f n
  -- ^ Argument with the @(k <= n)@ constraint
  -> (forall m . KnownNat m => f (m + k) -> r)
  -- ^ Function with the @(n + k)@ constraint
  -> r
leToPlusKN a f = f @ (n-k) a
{-# INLINE leToPlusKN #-}

-- | Change a function that has an argument with an @(k <= n)@ constraint to a
-- function with an argument that has an @(n + k)@ constraint.
--
-- __NB__ It is the dual to 'leToPlus'
--
-- === __Examples__
--
-- Example 1
--
-- @
-- f :: (1 '<=' n) => Index n -> Index n -> Bool
--
-- g :: Index (n + 1) -> Index (n + 1) -> Bool
-- g a b = 'plusToLe' \@1 $ \\a' -> 'plusToLe' \@1 $ \\b' -> f a' b'
-- @
--
-- Example 2
--
-- @
-- import Datal.Bifunctor.Flip
--
-- fold :: (1 '<=' n) => (a -> a -> a) -> Vec n a -> a
--
-- fold' :: (a -> a -> a) -> Vec (n+1) a -> a
-- fold' f a = 'plusToLe' \@1 (Flip a) (fold f . runFlip)
-- @
plusToLe
  :: forall (k :: Nat) n f r
   . f (n + k)
  -- ^ Argument with the @(n + k)@ constraint
  -> (forall m . (k <= m) => f m -> r)
  -- ^ Function with the @(k <= n)@ constraint
  -> r
plusToLe a f = f @(n + k) a
{-# INLINE plusToLe #-}

-- | Same as 'plusToLe' with added 'KnownNat' constraints
plusToLeKN
  :: forall (k :: Nat) n f r
   . (KnownNat n, KnownNat k)
  => f (n + k)
  -- ^ Argument with the @(n + k)@ constraint
  -> (forall m . (KnownNat m, k <= m) => f m -> r)
  -- ^ Function with the @(k <= n)@ constraint
  -> r
plusToLeKN a f = f @(n + k) a
