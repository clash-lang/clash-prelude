{-|
Copyright  :  (C) 2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

FPGA clock and reset components
-}

{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE MagicHash      #-}
{-# LANGUAGE TypeFamilies   #-}

{-# OPTIONS_HADDOCK show-extensions #-}

{-# LANGUAGE Trustworthy #-}

module CLaSH.TopEntity
  ( -- * Clock sources
    -- ** Altera clock sources
    altpll
  , alteraPll
    -- ** Xilinx clock sources
  , clockWizard
  , clockWizardDifferential
     -- * Reset synchronizers
  , resetSynchronizer
  )
where

import GHC.TypeLits

import CLaSH.Promoted.Symbol
import CLaSH.Sized.BitVector
import CLaSH.Signal.Internal

altpll :: (KnownSymbol nm, KnownNat period, dom ~ 'Domain nm period)
       => SSymbol pplName
       -> Signal dom Bit
       -> Reset 'Asynchronous dom -- ^ Active high
       -> (Clock 'Original dom,Signal dom Bit)
altpll _pllName _clkIn (Async rst) = (Clock (not1 (rst)),signal 1)
{-# NOINLINE altpll #-}

alteraPll :: (KnownSymbol nm, KnownNat period, dom ~ 'Domain nm period)
          => SSymbol pplName
          -> Signal dom Bit
          -> Reset 'Asynchronous dom -- ^ Active high
          -> (Clock 'Original dom,Signal dom Bit)
alteraPll _pllName _clkIn (Async rst) = (Clock (not1 (rst)),signal 1)
{-# NOINLINE alteraPll #-}

clockWizard :: (KnownSymbol nm, KnownNat period, dom ~ 'Domain nm period)
            => SSymbol pllName
            -> Signal dom Bit
            -> Reset 'Asynchronous dom -- ^ Active high
            -> (Clock 'Original dom,Signal dom Bit)
clockWizard _pllName _clkIn (Async rst) = (Clock (not1 (rst)),signal 1)
{-# NOINLINE clockWizard #-}

clockWizardDifferential :: (KnownSymbol nm, KnownNat period, dom ~ 'Domain nm period)
                        => SSymbol pllName
                        -> Signal dom Bit
                        -> Signal dom Bit
                        -> Reset 'Asynchronous dom -- ^ Active high
                        -> (Clock 'Original dom,Signal dom Bit)
clockWizardDifferential _pllName _clkIn1 _clkIn2 (Async rst) = (Clock (not1 (rst)),signal 1)
{-# NOINLINE clockWizardDifferential #-}

resetSynchronizer :: Reset 'Asynchronous domain
                  -> Clock clk domain
                  -> Reset 'Asynchronous domain
resetSynchronizer r c =
  let r1 = register# r c False (pure True)
      r2 = register# r c False r1
  in  unsafeToAsyncReset# r2
