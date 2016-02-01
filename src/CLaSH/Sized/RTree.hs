{-|
Copyright  :  (C) 2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE DataKinds, TypeOperators, GADTs, ScopedTypeVariables,
             KindSignatures, RankNTypes, TypeFamilies, UndecidableInstances,
             MagicHash, PatternSynonyms, FlexibleContexts #-}

{-# LANGUAGE Trustworthy #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module CLaSH.Sized.RTree where

import Data.Singletons.Prelude     (Apply, TyFun, type ($))
import Data.Proxy                  (Proxy (..))
import GHC.TypeLits                (KnownNat, Nat, type (+), type (^), type (*))
import qualified Prelude           as P
import Prelude                     hiding ((++), (!!))

import CLaSH.Class.BitPack         (BitPack (..))
import CLaSH.Promoted.Nat          (SNat (..), UNat (..), subSNat, powSNat, toUNat, snatToInteger)
import CLaSH.Promoted.Nat.Literals (d1, d2)
import CLaSH.Sized.Vector          (Vec (..), pattern (:>), (++), (!!))

data RTree :: Nat -> * -> * where
  LR :: a -> RTree 0 a
  BR :: RTree n a -> RTree n a -> RTree (n+1) a

instance Show a => Show (RTree n a) where
  show (LR a)   = show a
  show (BR l r) = '<':show l P.++ (',':show r) P.++ ">"

tfold :: forall p k a . KnownNat k
      => Proxy (p :: TyFun Nat * -> *)
      -> (a -> (p $ 0))
      -> (forall l . SNat l -> (p $ l) -> (p $ l) -> (p $ (l+1)))
      -> RTree k a
      -> (p $ k)
tfold _ f g = go SNat
  where
    go :: SNat m -> RTree m a -> (p $ m)
    go _  (LR a)   = f a
    go sn (BR l r) = let sn' = sn `subSNat` d1
                     in  g sn' (go sn' l) (go sn' r)
{-# NOINLINE tfold #-}

treplicate :: forall d a . SNat d -> a -> RTree d a
treplicate sn a = go (toUNat sn)
  where
    go :: UNat n -> RTree n a
    go UZero      = LR a
    go (USucc un) = BR (go un) (go un)
{-# NOINLINE treplicate #-}

data CTree (a :: *) (f :: TyFun Nat *) :: *
type instance Apply (CTree a) d = RTree d a

tmap :: KnownNat d => (a -> b) -> RTree d a -> RTree d b
tmap f = tfold (Proxy :: Proxy (CTree d)) (LR . f) (\_ l r -> BR l r)

data VTree (a :: *) (f :: TyFun Nat *) :: *
type instance Apply (VTree a) d = Vec (2^d) a

t2v :: KnownNat d => RTree d a -> Vec (2^d) a
t2v = tfold (Proxy :: Proxy (VTree a)) (:> Nil) (\_ l r -> l ++ r)

tindices :: KnownNat d => RTree d Integer
tindices = tfold (Proxy :: Proxy (CTree Integer)) LR
                 (\s@SNat l r-> BR l (tmap (+(snatToInteger (d2 `powSNat` s))) r))
                 (treplicate SNat 0)

v2t :: (KnownNat d, KnownNat (2^d)) => Vec (2^d) a -> RTree d a
v2t v = tmap (v !!) tindices

instance (KnownNat (2^d), KnownNat d, KnownNat (BitSize a), BitPack a) => BitPack (RTree d a) where
  type BitSize (RTree d a) = (2^d) * (BitSize a)
  pack   = pack . t2v
  unpack = v2t . unpack
