{-|
Copyright  :  (C) 2013-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

The Product/Signal isomorphism
-}

{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MagicHash              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}

{-# LANGUAGE Trustworthy #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module CLaSH.Signal.Bundle
  ( Bundle (..)
  )
where

import Control.Applicative   (liftA2)
import GHC.TypeLits          (KnownNat)
import Prelude               hiding (head, map, tail)

import CLaSH.Signal.Internal (Clock, Signal' (..))
import CLaSH.Sized.BitVector (BitVector)
import CLaSH.Sized.Fixed     (Fixed)
import CLaSH.Sized.Index     (Index)
import CLaSH.Sized.Signed    (Signed)
import CLaSH.Sized.Unsigned  (Unsigned)
import CLaSH.Sized.Vector    (Vec, traverse#)
import CLaSH.Sized.RTree     (RTree)

-- | Isomorphism between a 'CLaSH.Signal.Signal' of a product type (e.g. a tuple) and a
-- product type of 'CLaSH.Signal.Signal''s.
--
-- Instances of 'bundle must satisfy the following laws:
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
-- instance 'bundle D
-- @
--
-- is the same as:
--
-- @
-- data D = A | B
--
-- instance 'bundle D where
--   type 'Unbundled'' clk D = 'Signal'' clk D
--   'bundle'   _ s = s
--   'unbundle' _ s = s
-- @
--
class Bundle a where
  type Unbundled' (clk :: Clock) a = res | res -> clk
  type Unbundled' clk a = Signal' clk a
  -- | Example:
  --
  -- @
  -- __bundle__ :: ('Signal'' clk a, 'Signal'' clk b) -> 'Signal'' clk (a,b)
  -- @
  --
  -- However:
  --
  -- @
  -- __bundle__ :: 'Signal'' clk 'CLaSH.Sized.BitVector.Bit' -> 'Signal'' clk 'CLaSH.Sized.BitVector.Bit'
  -- @
  bundle :: Unbundled' clk a -> Signal' clk a

  {-# INLINE bundle #-}
  default bundle :: Signal' clk a -> Signal' clk a
  bundle s = s
  -- | Example:
  --
  -- @
  -- __unbundle__ :: 'Signal'' clk (a,b) -> ('Signal'' clk a, 'Signal'' clk b)
  -- @
  --
  -- However:
  --
  -- @
  -- __unbundle__ :: 'Signal'' clk 'CLaSH.Sized.BitVector.Bit' -> 'Signal'' clk 'CLaSH.Sized.BitVector.Bit'
  -- @
  unbundle :: Signal' clk a -> Unbundled' clk a

  {-# INLINE unbundle #-}
  default unbundle :: Signal' clk a -> Signal' clk a
  unbundle s = s

instance Bundle Bool
instance Bundle Integer
instance Bundle Int
instance Bundle Float
instance Bundle Double
instance Bundle ()
instance Bundle (Maybe a)
instance Bundle (Either a b)

instance Bundle (BitVector n)
instance Bundle (Index n)
instance Bundle (Fixed rep int frac)
instance Bundle (Signed n)
instance Bundle (Unsigned n)

instance Bundle (a,b) where
  type Unbundled' t (a,b) = (Signal' t a, Signal' t b)
  bundle       = uncurry (liftA2 (,))
  unbundle tup = (fmap fst tup, fmap snd tup)

instance Bundle (a,b,c) where
  type Unbundled' t (a,b,c) = (Signal' t a, Signal' t b, Signal' t c)
  bundle   (a,b,c) = (,,) <$> a <*> b <*> c
  unbundle tup     = (fmap (\(x,_,_) -> x) tup
                     ,fmap (\(_,x,_) -> x) tup
                     ,fmap (\(_,_,x) -> x) tup
                     )

instance Bundle (a,b,c,d) where
  type Unbundled' t (a,b,c,d) = ( Signal' t a, Signal' t b, Signal' t c
                                , Signal' t d
                                )
  bundle   (a,b,c,d) = (,,,) <$> a <*> b <*> c <*> d
  unbundle tup       = (fmap (\(x,_,_,_) -> x) tup
                       ,fmap (\(_,x,_,_) -> x) tup
                       ,fmap (\(_,_,x,_) -> x) tup
                       ,fmap (\(_,_,_,x) -> x) tup
                       )

instance Bundle (a,b,c,d,e) where
  type Unbundled' t (a,b,c,d,e) = ( Signal' t a, Signal' t b, Signal' t c
                                  , Signal' t d, Signal' t e
                                  )
  bundle   (a,b,c,d,e) = (,,,,) <$> a <*> b <*> c <*> d <*> e
  unbundle tup         = (fmap (\(x,_,_,_,_) -> x) tup
                         ,fmap (\(_,x,_,_,_) -> x) tup
                         ,fmap (\(_,_,x,_,_) -> x) tup
                         ,fmap (\(_,_,_,x,_) -> x) tup
                         ,fmap (\(_,_,_,_,x) -> x) tup
                         )

instance Bundle (a,b,c,d,e,f) where
  type Unbundled' t (a,b,c,d,e,f) = ( Signal' t a, Signal' t b, Signal' t c
                                    , Signal' t d, Signal' t e, Signal' t f
                                    )
  bundle   (a,b,c,d,e,f) = (,,,,,) <$> a <*> b <*> c <*> d <*> e <*> f
  unbundle tup           = (fmap (\(x,_,_,_,_,_) -> x) tup
                           ,fmap (\(_,x,_,_,_,_) -> x) tup
                           ,fmap (\(_,_,x,_,_,_) -> x) tup
                           ,fmap (\(_,_,_,x,_,_) -> x) tup
                           ,fmap (\(_,_,_,_,x,_) -> x) tup
                           ,fmap (\(_,_,_,_,_,x) -> x) tup
                           )

instance Bundle (a,b,c,d,e,f,g) where
  type Unbundled' t (a,b,c,d,e,f,g) = ( Signal' t a, Signal' t b, Signal' t c
                                      , Signal' t d, Signal' t e, Signal' t f
                                      , Signal' t g
                                      )
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
  type Unbundled' t (a,b,c,d,e,f,g,h) = ( Signal' t a, Signal' t b, Signal' t c
                                        , Signal' t d, Signal' t e, Signal' t f
                                        , Signal' t g, Signal' t h
                                        )
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
  type Unbundled' t (Vec n a) = Vec n (Signal' t a)
  -- The 'Traversable' instance of 'Vec' is not synthesisable, so we must
  -- define 'bundle' as a primitive.
  bundle   = vecBundle#
  unbundle = sequenceA

{-# NOINLINE vecBundle# #-}
vecBundle# :: Vec n (Signal' t a) -> Signal' t (Vec n a)
vecBundle# = traverse# id

instance KnownNat d => Bundle (RTree d a) where
  type Unbundled' t (RTree d a) = RTree d (Signal' t a)
  bundle   = sequenceA
  unbundle = sequenceA
