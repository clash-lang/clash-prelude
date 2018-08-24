{-|
Copyright  :  (C) 2013-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

Predefined 'SNat' singleton literals in the range [0 .. 1024]

Defines:

@
d0 = SNat :: SNat 0
d1 = SNat :: SNat 1
d2 = SNat :: SNat 2
...
d1024 = SNat :: SNat 1024
@

You can generate more 'SNat' literals using 'decLiteralsD' from "Clash.Promoted.Nat.TH"
-}

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds       #-}

{-# LANGUAGE Trustworthy #-}

{-# OPTIONS_HADDOCK show-extensions, prune #-}

module Clash.Promoted.Nat.Literals where

import Clash.Promoted.Nat.TH

$(decLiteralsD 0 1024)
