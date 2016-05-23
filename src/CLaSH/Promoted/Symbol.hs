{-|
Copyright  :  (C) 2013-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

{-# LANGUAGE Safe #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module CLaSH.Promoted.Symbol
  (SSymbol (..), ssymbolProxy, ssymbolToString)
where

import GHC.TypeLits (KnownSymbol, Symbol, symbolVal)

-- | Singleton value for a type-level string @s@
data SSymbol (s :: Symbol) where
  SSymbol :: KnownSymbol s => SSymbol s

instance Show (SSymbol s) where
  show s@SSymbol = symbolVal s

{-# INLINE ssymbolProxy #-}
-- | Create a singleton symbol literal @'SSymbol' s@ from a proxy for
-- /s/
ssymbolProxy :: KnownSymbol s => proxy s -> SSymbol s
ssymbolProxy _ = SSymbol

{-# INLINE ssymbolToString #-}
-- | Reify the type-level 'Symbol' @s@ to it's term-level 'String'
-- representation.
ssymbolToString :: SSymbol s -> String
ssymbolToString s@SSymbol = symbolVal s
