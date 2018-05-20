{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE NoImplicitPrelude      #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}

module Clash.Signal.Delayed.Bundle (
  Bundle,
  Unbundled,
  bundle,
  unbundle,
  ) where

import           Control.Applicative           (liftA2)
import           GHC.TypeLits                  (KnownNat)
import           Prelude                       hiding (head, map, tail)

import           Clash.Explicit.Signal.Delayed (DSignal, toSignal,
                                                unsafeFromSignal)
import qualified Clash.Signal.Bundle           as B

import           Clash.Signal.Internal         (Domain)
import           Clash.Sized.BitVector         (Bit, BitVector)
import           Clash.Sized.Fixed             (Fixed)
import           Clash.Sized.Index             (Index)
import           Clash.Sized.RTree             (RTree, lazyT)
import           Clash.Sized.Signed            (Signed)
import           Clash.Sized.Unsigned          (Unsigned)
import           Clash.Sized.Vector            (Vec, lazyV)

import           GHC.TypeLits                  (Nat)

-- | Isomorphism between a 'Clash.Explicit.Signal.Delayed' of a product type
-- (e.g. a tuple) and a product type of 'Clash.Explicit.Signal.Delayed''s.
--
-- Instances of 'Bundle' must satisfy the following laws:
--
-- @
-- 'bundle' . 'unbundle' = 'id'
-- 'unbundle' . 'bundle' = 'id'
-- @
--
-- By default, 'bundle' and 'unbundle', are defined as the identity, that is,
-- writing:
--
-- @
-- data D = A | B
--
-- instance Bundle D
-- @
--
-- is the same as:
--
-- @
-- data D = A | B
--
-- instance Bundle D where
--   type 'Unbundled'' domain delay D = 'DSignal'' domain d D
--   'bundle'   _ s = s
--   'unbundle' _ s = s
-- @
--
class Bundle a where
  type Unbundled (domain :: Domain) (d :: Nat) a = res | res -> domain d
  type Unbundled domain d a = DSignal domain d a

  -- | Example:
  --
  -- @
  -- __bundle__ :: ('DSignal' domain d a, 'DSignal' domain d b) -> 'DSignal' clk d (a,b)
  -- @
  --
  -- However:
  --
  -- @
  -- __bundle__ :: 'DSignal' domain 'Clash.Sized.BitVector.Bit' -> 'DSignal' domain 'Clash.Sized.BitVector.Bit'
  -- @
  bundle :: Unbundled domain d a -> DSignal domain d a
  {-# INLINE bundle #-}
  default bundle :: (DSignal domain d a ~ Unbundled domain d a)
                 => Unbundled domain d a -> DSignal domain d a
  bundle s = s
  -- | Example:
  --
  -- @
  -- __unbundle__ :: 'DSignal' domain d (a,b) -> ('DSignal' domain d a, 'DSignal' domain d b)
  -- @
  --
  -- However:
  --
  -- @
  -- __unbundle__ :: 'DSignal' domain 'Clash.Sized.BitVector.Bit' -> 'DSignal' domain 'Clash.Sized.BitVector.Bit'
  -- @
  unbundle :: DSignal domain d a -> Unbundled domain d a
  {-# INLINE unbundle #-}
  default unbundle :: (Unbundled domain d a ~ DSignal domain d a)
                   => DSignal domain d a -> Unbundled domain d a
  unbundle s = s

instance Bundle Bool
instance Bundle Integer
instance Bundle Int
instance Bundle Float
instance Bundle Double
instance Bundle (Maybe a)
instance Bundle (Either a b)

instance Bundle Bit
instance Bundle (BitVector n)
instance Bundle (Index n)
instance Bundle (Fixed rep int frac)
instance Bundle (Signed n)
instance Bundle (Unsigned n)

instance Bundle (a,b) where
  type Unbundled t delay (a,b) = (DSignal t delay a, DSignal t delay b)

  bundle       = uncurry (liftA2 (,))
  unbundle tup = (fmap fst tup, fmap snd tup)

instance Bundle (a,b,c) where
  type Unbundled t delay (a,b,c) =
    ( DSignal t delay a, DSignal t delay b, DSignal t delay c)

  bundle   (a,b,c) = (,,) <$> a <*> b <*> c
  unbundle tup     = (fmap (\(x,_,_) -> x) tup
                      ,fmap (\(_,x,_) -> x) tup
                      ,fmap (\(_,_,x) -> x) tup
                      )
instance Bundle (a,b,c,d) where
  type Unbundled t delay (a,b,c,d) =
    ( DSignal t delay a, DSignal t delay b, DSignal t delay c, DSignal t delay d)

  bundle   (a,b,c,d) = (,,,) <$> a <*> b <*> c <*> d
  unbundle tup     = (fmap (\(x,_,_,_) -> x) tup
                      ,fmap (\(_,x,_,_) -> x) tup
                      ,fmap (\(_,_,x,_) -> x) tup
                      ,fmap (\(_,_,_,x) -> x) tup
                      )

instance Bundle (a,b,c,d,e) where
  type Unbundled t delay (a,b,c,d,e) =
    ( DSignal t delay a, DSignal t delay b, DSignal t delay c, DSignal t delay d
    , DSignal t delay e)

  bundle   (a,b,c,d,e) = (,,,,) <$> a <*> b <*> c <*> d <*> e
  unbundle tup     = (fmap (\(x,_,_,_,_) -> x) tup
                      ,fmap (\(_,x,_,_,_) -> x) tup
                      ,fmap (\(_,_,x,_,_) -> x) tup
                      ,fmap (\(_,_,_,x,_) -> x) tup
                      ,fmap (\(_,_,_,_,x) -> x) tup
                      )

instance Bundle (a,b,c,d,e,f) where
  type Unbundled t delay (a,b,c,d,e,f) =
    ( DSignal t delay a, DSignal t delay b, DSignal t delay c, DSignal t delay d
    , DSignal t delay e, DSignal t delay f)

  bundle   (a,b,c,d,e,f) = (,,,,,) <$> a <*> b <*> c <*> d <*> e <*> f
  unbundle tup           = (fmap (\(x,_,_,_,_,_) -> x) tup
                           ,fmap (\(_,x,_,_,_,_) -> x) tup
                           ,fmap (\(_,_,x,_,_,_) -> x) tup
                           ,fmap (\(_,_,_,x,_,_) -> x) tup
                           ,fmap (\(_,_,_,_,x,_) -> x) tup
                           ,fmap (\(_,_,_,_,_,x) -> x) tup
                           )

instance Bundle (a,b,c,d,e,f,g) where
  type Unbundled t delay (a,b,c,d,e,f,g) =
    ( DSignal t delay a, DSignal t delay b, DSignal t delay c, DSignal t delay d
    , DSignal t delay e, DSignal t delay f, DSignal t delay g)

  bundle   (a,b,c,d,e,f,g) = (,,,,,,) <$> a <*> b <*> c <*> d <*> e <*> f
                                      <*> g
  unbundle tup             = (fmap (\(x,_,_,_,_,_,_) -> x) tup
                             ,fmap (\(_,x,_,_,_,_,_) -> x) tup
                             ,fmap (\(_,_,x,_,_,_,_) -> x) tup
                             ,fmap (\(_,_,_,x,_,_,_) -> x) tup
                             ,fmap (\(_,_,_,_,x,_,_) -> x) tup
                             ,fmap (\(_,_,_,_,_,x,_) -> x) tup
                             ,fmap (\(_,_,_,_,_,_,x) -> x) tup
                             )

instance Bundle (a,b,c,d,e,f,g,h) where
  type Unbundled t delay (a,b,c,d,e,f,g,h) =
    ( DSignal t delay a, DSignal t delay b, DSignal t delay c, DSignal t delay d
    , DSignal t delay e, DSignal t delay f ,DSignal t delay g, DSignal t delay h)

  bundle   (a,b,c,d,e,f,g,h) = (,,,,,,,) <$> a <*> b <*> c <*> d <*> e <*> f
                                         <*> g <*> h
  unbundle tup               = (fmap (\(x,_,_,_,_,_,_,_) -> x) tup
                               ,fmap (\(_,x,_,_,_,_,_,_) -> x) tup
                               ,fmap (\(_,_,x,_,_,_,_,_) -> x) tup
                               ,fmap (\(_,_,_,x,_,_,_,_) -> x) tup
                               ,fmap (\(_,_,_,_,x,_,_,_) -> x) tup
                               ,fmap (\(_,_,_,_,_,x,_,_) -> x) tup
                               ,fmap (\(_,_,_,_,_,_,x,_) -> x) tup
                               ,fmap (\(_,_,_,_,_,_,_,x) -> x) tup
                               )

instance KnownNat n => Bundle (Vec n a) where
  type Unbundled t d (Vec n a) = Vec n (DSignal t d a)
  bundle   = unsafeFromSignal . B.bundle . fmap toSignal
  unbundle = sequenceA . fmap lazyV

instance KnownNat d => Bundle (RTree d a) where
  type Unbundled t delay (RTree d a) = RTree d (DSignal t delay a)
  bundle   = sequenceA
  unbundle = sequenceA . fmap lazyT

