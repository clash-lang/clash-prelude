{-|
Copyright  :  (C) 2015-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE KindSignatures  #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeOperators   #-}
module CLaSH.Sized.Vector where

import GHC.TypeLits  (KnownNat, Nat, type (+))
import {-# SOURCE #-} CLaSH.Sized.Internal.BitVector (BitVector, Bit)

type role Vec nominal representational
data Vec :: Nat -> * -> *

instance (KnownNat m, (~) m ((+) n 1)) => Foldable (Vec m)

bv2v  :: KnownNat n => BitVector n -> Vec n Bit
map   :: (a -> b) -> Vec n a -> Vec n b
foldr :: (a -> b -> b) -> b -> Vec n a -> b
foldl :: (b -> a -> b) -> b -> Vec n a -> b
