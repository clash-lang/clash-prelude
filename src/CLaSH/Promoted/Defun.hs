{-|
Copyright  :  (C) 2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

Temporary definitions for 'TyFun', 'Apply', and ('@@') until singletons
compiles on GHC8
-}

{-# LANGUAGE DataKinds, KindSignatures, PolyKinds, TypeFamilies, TypeOperators,
             UndecidableInstances #-}

module CLaSH.Promoted.Defun where

-- | Representation of the kind of a type-level function. The difference
-- between term-level arrows and this type-level arrow is that at the term
-- level applications can be unsaturated, whereas at the type level all
-- applications have to be fully saturated.
data TyFun :: * -> * -> *

-- | Type level function application
type family Apply (f :: TyFun k1 k2 -> *) (x :: k1) :: k2

-- | An infix synonym for `Apply`
type a @@ b = Apply a b
infixl 9 @@
