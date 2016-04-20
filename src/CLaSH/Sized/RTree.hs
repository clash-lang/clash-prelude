{-|
Copyright  :  (C) 2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE DataKinds, TypeOperators, GADTs, ScopedTypeVariables,
             KindSignatures, RankNTypes, TypeFamilies, UndecidableInstances,
             MagicHash, PatternSynonyms, FlexibleContexts, TupleSections,
             ViewPatterns #-}

{-# LANGUAGE Trustworthy #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module CLaSH.Sized.RTree
  ( -- * 'RTree' data type
    RTree (..)
  , pattern LR
  , pattern BR
    -- * Construction
  , treplicate
  , trepeat
    -- * Accessors
    -- ** Indexing
  , indexTree
  , tindices
    -- * Modifying trees
  , replaceTree
    -- * Element-wise operations
    -- ** Mapping
  , tmap
  , tzipWith
    -- ** Zipping
  , tzip
    -- ** Unzipping
  , tunzip
    -- * Folding
  , tfold
    -- ** Specialised folds
  , tdfold
    -- * Conversions
  , v2t
  , t2v
  )
where

import Control.Applicative         (liftA2)
import qualified Control.Lens      as Lens
-- import Data.Singletons.Prelude     (Apply, TyFun, type ($))
import Data.Proxy                  (Proxy (..))
import GHC.TypeLits                (KnownNat, Nat, type (+), type (^), type (*))
import qualified Prelude           as P
import Prelude                     hiding ((++), (!!))

import CLaSH.Class.BitPack         (BitPack (..))
import CLaSH.Promoted.Defun        (TyFun,Apply,type (@@))
import CLaSH.Promoted.Nat          (SNat (..), UNat (..), powSNat, snatToInteger,
                                    subSNat, toUNat)
import CLaSH.Promoted.Nat.Literals (d1, d2)
import CLaSH.Sized.Index           (Index)
import CLaSH.Sized.Vector          (Vec (..), (!!), (++), dtfold, replace)

data RTree :: Nat -> * -> * where
  LR_ :: a -> RTree 0 a
  BR_ :: RTree d a -> RTree d a -> RTree (d+1) a
{-# WARNING LR_ "Use 'LR' instead of 'LR_'" #-}
{-# WARNING BR_ "Use 'BR' instead of 'BR_'" #-}

textract :: RTree 0 a -> a
textract (LR_ x) = x
{-# NOINLINE textract #-}

tsplit :: RTree (d+1) a -> (RTree d a,RTree d a)
tsplit (BR_ l r) = (l,r)
{-# NOINLINE tsplit #-}

pattern LR :: a -> RTree 0 a
pattern LR x <- (textract -> x)
  where
    LR x = LR_ x

pattern BR :: RTree d a -> RTree d a -> RTree (d+1) a
pattern BR l r <- ((\t -> (tsplit t)) -> (l,r))
  where
    BR l r = BR_ l r

instance Show a => Show (RTree n a) where
  show (LR_ a)   = show a
  show (BR_ l r) = '<':show l P.++ (',':show r) P.++ ">"

instance KnownNat d => Functor (RTree d) where
  fmap = tmap

instance KnownNat d => Applicative (RTree d) where
  pure  = trepeat
  (<*>) = tzipWith ($)

instance KnownNat d => Foldable (RTree d) where
  foldMap f = tfold f mappend

data TraversableTree (g :: * -> *) (a :: *) (f :: TyFun Nat *) :: *
type instance Apply (TraversableTree f a) d = f (RTree d a)

instance KnownNat d => Traversable (RTree d) where
  traverse f = tdfold (Proxy :: Proxy (TraversableTree f b))
                      (fmap LR . f)
                      (const (liftA2 BR))

instance (KnownNat (2^d), KnownNat d, KnownNat (BitSize a), BitPack a) =>
  BitPack (RTree d a) where
  type BitSize (RTree d a) = (2^d) * (BitSize a)
  pack   = pack . t2v
  unpack = v2t . unpack

type instance Lens.Index   (RTree d a) = Int
type instance Lens.IxValue (RTree d a) = a
instance (KnownNat d, KnownNat (2^d)) => Lens.Ixed (RTree d a) where
  ix i f t = replaceTree i <$> f (indexTree t i) <*> pure t

tdfold :: forall p k a . KnownNat k
       => Proxy (p :: TyFun Nat * -> *)
       -> (a -> (p @@ 0))
       -> (forall l . SNat l -> (p @@ l) -> (p @@ l) -> (p @@ (l+1)))
       -> RTree k a
       -> (p @@ k)
tdfold _ f g = go SNat
  where
    go :: SNat m -> RTree m a -> (p @@ m)
    go _  (LR_ a)   = f a
    go sn (BR_ l r) = let sn' = sn `subSNat` d1
                      in  g sn' (go sn' l) (go sn' r)
{-# NOINLINE tdfold #-}

data TfoldTree (a :: *) (f :: TyFun Nat *) :: *
type instance Apply (TfoldTree a) d = a

tfold :: KnownNat d
      => (a -> b)
      -> (b -> b -> b)
      -> RTree d a
      -> b
tfold f g = tdfold (Proxy :: Proxy (TfoldTree b)) f (const g)

treplicate :: forall d a . SNat d -> a -> RTree d a
treplicate sn a = go (toUNat sn)
  where
    go :: UNat n -> RTree n a
    go UZero      = LR a
    go (USucc un) = BR (go un) (go un)
{-# NOINLINE treplicate #-}

trepeat :: KnownNat d => a -> RTree d a
trepeat = treplicate SNat

data MapTree (a :: *) (f :: TyFun Nat *) :: *
type instance Apply (MapTree a) d = RTree d a

tmap :: KnownNat d => (a -> b) -> RTree d a -> RTree d b
tmap f = tdfold (Proxy :: Proxy (MapTree b)) (LR . f) (\_ l r -> BR l r)

tindices :: (KnownNat d, KnownNat (2^d)) => RTree d (Index (2^d))
tindices =
  tdfold (Proxy :: Proxy (MapTree (Index (2^d)))) LR
         (\s@SNat l r -> BR l (tmap (+(fromInteger (snatToInteger (d2 `powSNat` s)))) r))
         (treplicate SNat 0)

data V2TTree (a :: *) (f :: TyFun Nat *) :: *
type instance Apply (V2TTree a) d = RTree d a

v2t :: KnownNat d => Vec (2^d) a -> RTree d a
v2t = dtfold (Proxy :: Proxy (V2TTree a)) LR (const BR)

data T2VTree (a :: *) (f :: TyFun Nat *) :: *
type instance Apply (T2VTree a) d = Vec (2^d) a

t2v :: KnownNat d => RTree d a -> Vec (2^d) a
t2v = tdfold (Proxy :: Proxy (T2VTree a)) (:> Nil) (\_ l r -> l ++ r)

indexTree :: (KnownNat d, KnownNat (2^d), Enum i) => RTree d a -> i -> a
indexTree t i = (t2v t) !! i

replaceTree :: (KnownNat d, KnownNat (2^d), Enum i) => i -> a -> RTree d a -> RTree d a
replaceTree i a = v2t . replace i a . t2v

data ZipWithTree (b :: *) (c :: *) (f :: TyFun Nat *) :: *
type instance Apply (ZipWithTree b c) d = RTree d b -> RTree d c

tzipWith :: forall a b c d . KnownNat d => (a -> b -> c) -> RTree d a -> RTree d b -> RTree d c
tzipWith f = tdfold (Proxy :: Proxy (ZipWithTree b c)) lr br
  where
    lr :: a -> RTree 0 b -> RTree 0 c
    lr a (LR b) = LR (f a b)
    lr _ _      = error "impossible"

    br :: SNat l
       -> (RTree l b -> RTree l c)
       -> (RTree l b -> RTree l c)
       -> RTree (l+1) b
       -> RTree (l+1) c
    br _ fl fr (BR l r) = BR (fl l) (fr r)
    br _ _  _  _        = error "impossible"

tzip :: KnownNat d => RTree d a -> RTree d b -> RTree d (a,b)
tzip = tzipWith (,)

data UnzipTree (a :: *) (b :: *) (f :: TyFun Nat *) :: *
type instance Apply (UnzipTree a b) d = (RTree d a, RTree d b)

tunzip :: KnownNat d => RTree d (a,b) -> (RTree d a,RTree d b)
tunzip = tdfold (Proxy :: Proxy (UnzipTree a b)) lr br
  where
    lr   (a,b) = (LR a,LR b)

    br _ (l1,r1) (l2,r2) = (BR l1 l2, BR r1 r2)
