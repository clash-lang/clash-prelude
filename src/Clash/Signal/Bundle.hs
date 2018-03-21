{-|
Copyright  :  (C) 2013-2016, University of Twente,
                  2017     , Myrtle Software Ltd, Google Inc.
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

The Product/Signal isomorphism
-}

{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE DefaultSignatures       #-}
{-# LANGUAGE KindSignatures          #-}
{-# LANGUAGE MagicHash               #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeFamilyDependencies  #-}
{-# LANGUAGE TypeOperators           #-}

{-# LANGUAGE Trustworthy #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module Clash.Signal.Bundle
  ( Bundle (..)
  , DBundle
  )
where

import Control.Applicative   (liftA2)
import GHC.TypeLits          (KnownNat)
import GHC.Types             (Constraint)
import Prelude               hiding (head, map, tail)

import Clash.NamedTypes      ((:::))
import Clash.Signal.Internal (Domain, Signal (..))
import Clash.Sized.BitVector (Bit, BitVector)
import Clash.Sized.Fixed     (Fixed)
import Clash.Sized.Index     (Index)
import Clash.Sized.Signed    (Signed)
import Clash.Sized.Unsigned  (Unsigned)
import Clash.Sized.Vector    (Vec, traverse#, lazyV)
import Clash.Sized.RTree     (RTree, lazyT)

-- | Isomorphism between a 'Clash.Signal.Signal' of a product type (e.g. a tuple) and a
-- product type of 'Clash.Signal.Signal''s.
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
  type Unbundled (domain :: Domain) a = res | res -> domain
  type Unbundled domain a = Signal domain a
  -- | Example:
  --
  -- @
  -- __bundle__ :: ('Signal' domain a, 'Signal' domain b) -> 'Signal' clk (a,b)
  -- @
  --
  -- However:
  --
  -- @
  -- __bundle__ :: 'Signal' domain 'Clash.Sized.BitVector.Bit' -> 'Signal' domain 'Clash.Sized.BitVector.Bit'
  -- @
  bundle :: Unbundled domain a -> Signal domain a

  {-# INLINE bundle #-}
  default bundle :: (Signal domain a ~ Unbundled domain a)
                 => Unbundled domain a -> Signal domain a
  bundle s = s
  -- | Example:
  --
  -- @
  -- __unbundle__ :: 'Signal' domain (a,b) -> ('Signal' domain a, 'Signal' domain b)
  -- @
  --
  -- However:
  --
  -- @
  -- __unbundle__ :: 'Signal' domain 'Clash.Sized.BitVector.Bit' -> 'Signal' domain 'Clash.Sized.BitVector.Bit'
  -- @
  unbundle :: Signal domain a -> Unbundled domain a

  {-# INLINE unbundle #-}
  default unbundle :: (Unbundled domain a ~ Signal domain a)
                   => Signal domain a -> Unbundled domain a
  unbundle s = s

  type DUnbundled (domain :: Domain) a = res | res -> domain
  type DUnbundled domain a = Signal domain a

  type DBundle' a :: Constraint
  type DBundle' a = ()

  -- | Example:
  --
  -- @
  -- __deepBundle__ :: ('Signal' domain a, ('Signal' domain b, 'Signal' domain c)) -> 'Signal' clk (a,(b,c))
  -- @
  --
  -- However:
  --
  -- @
  -- __deepBundle__ :: 'Signal' domain 'Clash.Sized.BitVector.Bit' -> 'Signal' domain 'Clash.Sized.BitVector.Bit'
  -- @
  deepBundle :: DBundle' a => DUnbundled domain a -> Signal domain a
  {-# INLINE deepBundle #-}

  default deepBundle
    :: (Signal domain a ~ DUnbundled domain a)
    => DUnbundled domain a -> Signal domain a
  deepBundle s = s

  -- | Example:
  --
  -- @
  -- __deepUnbundle__ :: 'Signal' domain (a,(b,c)) -> ('Signal' domain a, ('Signal' domain b, 'Signal' domain c))
  -- @
  --
  -- However:
  --
  -- @
  -- __deepUnbundle__ :: 'Signal' domain 'Clash.Sized.BitVector.Bit' -> 'Signal' domain 'Clash.Sized.BitVector.Bit'
  -- @
  deepUnbundle :: DBundle' a => Signal domain a -> DUnbundled domain a
  {-# INLINE deepUnbundle #-}

  default deepUnbundle
    :: (DUnbundled domain a ~ Signal domain a)
    => Signal domain a -> DUnbundled domain a
  deepUnbundle s = s

type DBundle a = (Bundle a, DBundle' a)

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

-- | Note that:
--
-- > bundle   :: () -> Signal domain ()
-- > unbundle :: Signal domain () -> ()
instance Bundle () where
  type Unbundled t () = t ::: ()
  -- ^ This is just to satisfy the injectivity annotation
  bundle   u = pure u
  unbundle _ = ()

instance Bundle (a,b) where
  type Unbundled t (a,b) = (Signal t a, Signal t b)
  bundle       = uncurry (liftA2 (,))
  unbundle tup = (fmap fst tup, fmap snd tup)

  type DUnbundled t (a,b) = (DUnbundled t a, DUnbundled t b)
  type DBundle' (a,b) = (DBundle a, DBundle b)
  deepBundle (a,b) = (,) <$> deepBundle a
                         <*> deepBundle b
  deepUnbundle tup = (deepUnbundle (fmap fst tup)
                     ,deepUnbundle (fmap snd tup)
                     )


instance Bundle (a,b,c) where
  type Unbundled t (a,b,c) = (Signal t a, Signal t b, Signal t c)
  bundle   (a,b,c) = (,,) <$> a <*> b <*> c
  unbundle tup     = (fmap (\(x,_,_) -> x) tup
                     ,fmap (\(_,x,_) -> x) tup
                     ,fmap (\(_,_,x) -> x) tup
                     )

  type DUnbundled t (a,b,c) = (DUnbundled t a, DUnbundled t b, DUnbundled t c)
  type DBundle' (a,b,c) = (DBundle a, DBundle b, DBundle c)
  deepBundle (a,b,c) = (,,) <$> deepBundle a
                            <*> deepBundle b
                            <*> deepBundle c
  deepUnbundle tup = (deepUnbundle (fmap (\(x,_,_) -> x) tup)
                     ,deepUnbundle (fmap (\(_,x,_) -> x) tup)
                     ,deepUnbundle (fmap (\(_,_,x) -> x) tup)
                     )

instance Bundle (a,b,c,d) where
  type Unbundled t (a,b,c,d) = ( Signal t a, Signal t b, Signal t c
                               , Signal t d
                               )
  bundle   (a,b,c,d) = (,,,) <$> a <*> b <*> c <*> d
  unbundle tup       = (fmap (\(x,_,_,_) -> x) tup
                       ,fmap (\(_,x,_,_) -> x) tup
                       ,fmap (\(_,_,x,_) -> x) tup
                       ,fmap (\(_,_,_,x) -> x) tup
                       )

  type DUnbundled t (a,b,c,d) = ( DUnbundled t a, DUnbundled t b, DUnbundled t c
                                , DUnbundled t d
                                )
  type DBundle' (a,b,c,d) = (DBundle a, DBundle b, DBundle c, DBundle d)
  deepBundle   (a,b,c,d) = (,,,) <$> deepBundle a
                                 <*> deepBundle b
                                 <*> deepBundle c
                                 <*> deepBundle d
  deepUnbundle tup       = (deepUnbundle (fmap (\(x,_,_,_) -> x) tup)
                           ,deepUnbundle (fmap (\(_,x,_,_) -> x) tup)
                           ,deepUnbundle (fmap (\(_,_,x,_) -> x) tup)
                           ,deepUnbundle (fmap (\(_,_,_,x) -> x) tup)
                           )

instance Bundle (a,b,c,d,e) where
  type Unbundled t (a,b,c,d,e) = ( Signal t a, Signal t b, Signal t c
                                 , Signal t d, Signal t e
                                 )
  bundle   (a,b,c,d,e) = (,,,,) <$> a <*> b <*> c <*> d <*> e
  unbundle tup         = (fmap (\(x,_,_,_,_) -> x) tup
                         ,fmap (\(_,x,_,_,_) -> x) tup
                         ,fmap (\(_,_,x,_,_) -> x) tup
                         ,fmap (\(_,_,_,x,_) -> x) tup
                         ,fmap (\(_,_,_,_,x) -> x) tup
                         )

  type DUnbundled t (a,b,c,d,e) = ( DUnbundled t a, DUnbundled t b, DUnbundled t c
                                  , DUnbundled t d, DUnbundled t e
                                  )
  type DBundle' (a,b,c,d,e) = ( DBundle a, DBundle b, DBundle c, DBundle d
                              , DBundle e
                              )
  deepBundle   (a,b,c,d,e) = (,,,,) <$> deepBundle a
                                    <*> deepBundle b
                                    <*> deepBundle c
                                    <*> deepBundle d
                                    <*> deepBundle e
  deepUnbundle tup         = (deepUnbundle (fmap (\(x,_,_,_,_) -> x) tup)
                             ,deepUnbundle (fmap (\(_,x,_,_,_) -> x) tup)
                             ,deepUnbundle (fmap (\(_,_,x,_,_) -> x) tup)
                             ,deepUnbundle (fmap (\(_,_,_,x,_) -> x) tup)
                             ,deepUnbundle (fmap (\(_,_,_,_,x) -> x) tup)
                             )

instance Bundle (a,b,c,d,e,f) where
  type Unbundled t (a,b,c,d,e,f) = ( Signal t a, Signal t b, Signal t c
                                   , Signal t d, Signal t e, Signal t f
                                   )
  bundle   (a,b,c,d,e,f) = (,,,,,) <$> a <*> b <*> c <*> d <*> e <*> f
  unbundle tup           = (fmap (\(x,_,_,_,_,_) -> x) tup
                           ,fmap (\(_,x,_,_,_,_) -> x) tup
                           ,fmap (\(_,_,x,_,_,_) -> x) tup
                           ,fmap (\(_,_,_,x,_,_) -> x) tup
                           ,fmap (\(_,_,_,_,x,_) -> x) tup
                           ,fmap (\(_,_,_,_,_,x) -> x) tup
                           )

  type DUnbundled t (a,b,c,d,e,f) = ( DUnbundled t a, DUnbundled t b, DUnbundled t c
                                    , DUnbundled t d, DUnbundled t e, DUnbundled t f
                                    )
  type DBundle' (a,b,c,d,e,f) = ( DBundle a, DBundle b, DBundle c, DBundle d
                                , DBundle e, DBundle f
                                )
  deepBundle   (a,b,c,d,e,f) = (,,,,,) <$> deepBundle a
                                       <*> deepBundle b
                                       <*> deepBundle c
                                       <*> deepBundle d
                                       <*> deepBundle e
                                       <*> deepBundle f
  deepUnbundle tup           = (deepUnbundle (fmap (\(x,_,_,_,_,_) -> x) tup)
                               ,deepUnbundle (fmap (\(_,x,_,_,_,_) -> x) tup)
                               ,deepUnbundle (fmap (\(_,_,x,_,_,_) -> x) tup)
                               ,deepUnbundle (fmap (\(_,_,_,x,_,_) -> x) tup)
                               ,deepUnbundle (fmap (\(_,_,_,_,x,_) -> x) tup)
                               ,deepUnbundle (fmap (\(_,_,_,_,_,x) -> x) tup)
                               )

instance Bundle (a,b,c,d,e,f,g) where
  type Unbundled t (a,b,c,d,e,f,g) = ( Signal t a, Signal t b, Signal t c
                                     , Signal t d, Signal t e, Signal t f
                                     , Signal t g
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

  type DUnbundled t (a,b,c,d,e,f,g) = ( DUnbundled t a, DUnbundled t b, DUnbundled t c
                                      , DUnbundled t d, DUnbundled t e, DUnbundled t f
                                      , DUnbundled t g
                                      )
  type DBundle' (a,b,c,d,e,f,g) = ( DBundle a, DBundle b, DBundle c, DBundle d
                                  , DBundle e, DBundle f, DBundle g
                                  )
  deepBundle   (a,b,c,d,e,f,g) = (,,,,,,) <$> deepBundle a
                                          <*> deepBundle b
                                          <*> deepBundle c
                                          <*> deepBundle d
                                          <*> deepBundle e
                                          <*> deepBundle f
                                          <*> deepBundle g
  deepUnbundle tup             = (deepUnbundle (fmap (\(x,_,_,_,_,_,_) -> x) tup)
                                 ,deepUnbundle (fmap (\(_,x,_,_,_,_,_) -> x) tup)
                                 ,deepUnbundle (fmap (\(_,_,x,_,_,_,_) -> x) tup)
                                 ,deepUnbundle (fmap (\(_,_,_,x,_,_,_) -> x) tup)
                                 ,deepUnbundle (fmap (\(_,_,_,_,x,_,_) -> x) tup)
                                 ,deepUnbundle (fmap (\(_,_,_,_,_,x,_) -> x) tup)
                                 ,deepUnbundle (fmap (\(_,_,_,_,_,_,x) -> x) tup)
                                 )

instance Bundle (a,b,c,d,e,f,g,h) where
  type Unbundled t (a,b,c,d,e,f,g,h) = ( Signal t a, Signal t b, Signal t c
                                       , Signal t d, Signal t e, Signal t f
                                       , Signal t g, Signal t h
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

  type DUnbundled t (a,b,c,d,e,f,g,h) = ( DUnbundled t a, DUnbundled t b, DUnbundled t c
                                        , DUnbundled t d, DUnbundled t e, DUnbundled t f
                                        , DUnbundled t g, DUnbundled t h
                                        )
  type DBundle' (a,b,c,d,e,f,g,h) = ( DBundle a, DBundle b, DBundle c, DBundle d
                                    , DBundle e, DBundle f, DBundle g, DBundle h
                                    )
  deepBundle   (a,b,c,d,e,f,g,h) = (,,,,,,,) <$> deepBundle a
                                             <*> deepBundle b
                                             <*> deepBundle c
                                             <*> deepBundle d
                                             <*> deepBundle e
                                             <*> deepBundle f
                                             <*> deepBundle g
                                             <*> deepBundle h
  deepUnbundle tup               = (deepUnbundle (fmap (\(x,_,_,_,_,_,_,_) -> x) tup)
                                   ,deepUnbundle (fmap (\(_,x,_,_,_,_,_,_) -> x) tup)
                                   ,deepUnbundle (fmap (\(_,_,x,_,_,_,_,_) -> x) tup)
                                   ,deepUnbundle (fmap (\(_,_,_,x,_,_,_,_) -> x) tup)
                                   ,deepUnbundle (fmap (\(_,_,_,_,x,_,_,_) -> x) tup)
                                   ,deepUnbundle (fmap (\(_,_,_,_,_,x,_,_) -> x) tup)
                                   ,deepUnbundle (fmap (\(_,_,_,_,_,_,x,_) -> x) tup)
                                   ,deepUnbundle (fmap (\(_,_,_,_,_,_,_,x) -> x) tup)
                                   )

instance KnownNat n => Bundle (Vec n a) where
  type Unbundled t (Vec n a) = Vec n (Signal t a)
  -- The 'Traversable' instance of 'Vec' is not synthesisable, so we must
  -- define 'bundle' as a primitive.
  bundle   = vecBundle#
  unbundle = sequenceA . fmap lazyV

  type DUnbundled t (Vec n a) = Vec n (DUnbundled t a)
  type DBundle' (Vec n a) = DBundle a
  deepBundle   = vecBundle# . fmap deepBundle
  deepUnbundle = fmap deepUnbundle . sequenceA . fmap lazyV

{-# NOINLINE vecBundle# #-}
vecBundle# :: Vec n (Signal t a) -> Signal t (Vec n a)
vecBundle# = traverse# id

instance KnownNat d => Bundle (RTree d a) where
  type Unbundled t (RTree d a) = RTree d (Signal t a)
  bundle   = sequenceA
  unbundle = sequenceA . fmap lazyT

  type DUnbundled t (RTree d a) = RTree d (DUnbundled t a)
  type DBundle' (RTree d a) = DBundle a
  deepBundle   = sequenceA . fmap deepBundle
  deepUnbundle = fmap deepUnbundle . sequenceA . fmap lazyT
