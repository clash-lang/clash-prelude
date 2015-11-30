{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
module CLaSH.Prelude.ElimClocks where

import GHC.TypeLits          (KnownNat, KnownSymbol)

import CLaSH.Signal.Explicit (SClock, Clock(..), sclock)

type family ElimClocks a where
  ElimClocks (SClock ('Clk s p) -> a) = ElimClocks a
  ElimClocks (b                 -> a) = b -> ElimClocks a
  ElimClocks a                        = a

class ElimClocks a ~ b => NeedsClocks a b where
  -- | Fill in clock-line arguments, for easy use on the REPL
  --
  -- The clock-line arguments are used by the CLaSH compiler to infer the proper
  -- nets, but don't actually matter for simulation in Haskell. This function
  -- just fills them in with dummy arguments, as there is no "real" clock to
  -- connect them to.
  --
  -- >>> :{
  -- let g :: SClock ('Clk "asdf" 100)
  --       -> Int
  --       -> SClock ('Clk "qwer" 99)
  --       -> Int
  --     g _ i _ = i
  -- :}
  -- >>> :{
  -- let f :: Int -> Int
  --     f = provideClocks g
  -- :}
  --
  -- __NB__: This function is not synthesisable
  provideClocks :: a -> b

instance (KnownNat p, KnownSymbol s, NeedsClocks a b)
    => NeedsClocks (SClock ('Clk s p) -> a) b where
  provideClocks f = provideClocks $ f sclock

instance (NeedsClocks a c, ElimClocks (b -> a) ~ (b -> ElimClocks a))
    => NeedsClocks (b -> a) (b -> c) where
  provideClocks f = \b -> provideClocks $ f b

instance a ~ ElimClocks a
    => NeedsClocks a a where
  provideClocks = id
