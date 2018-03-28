{-|
Copyright  :  (C) 2013-2016, University of Twente,
                  2016-2017, Myrtle Software Ltd,
                  2017     , Google Inc.
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>

BlockRAM primitives

= Using RAMs #usingrams#

We will show a rather elaborate example on how you can, and why you might want
to use 'blockRam's. We will build a \"small\" CPU+Memory+Program ROM where we
will slowly evolve to using blockRams. Note that the code is /not/ meant as a
de-facto standard on how to do CPU design in CλaSH.

We start with the definition of the Instructions, Register names and machine
codes:

@
{\-\# LANGUAGE RecordWildCards, TupleSections \#-\}
module CPU where

import Clash.Prelude

type InstrAddr = Unsigned 8
type MemAddr   = Unsigned 5
type Value     = Signed 8

data Instruction
  = Compute Operator Reg Reg Reg
  | Branch Reg Value
  | Jump Value
  | Load MemAddr Reg
  | Store Reg MemAddr
  | Nop
  deriving (Eq,Show)

data Reg
  = Zero
  | PC
  | RegA
  | RegB
  | RegC
  | RegD
  | RegE
  deriving (Eq,Show,Enum)

data Operator = Add | Sub | Incr | Imm | CmpGt
  deriving (Eq,Show)

data MachCode
  = MachCode
  { inputX  :: Reg
  , inputY  :: Reg
  , result  :: Reg
  , aluCode :: Operator
  , ldReg   :: Reg
  , rdAddr  :: MemAddr
  , wrAddrM :: Maybe MemAddr
  , jmpM    :: Maybe Value
  }

nullCode = MachCode { inputX = Zero, inputY = Zero, result = Zero, aluCode = Imm
                    , ldReg = Zero, rdAddr = 0, wrAddrM = Nothing
                    , jmpM = Nothing
                    }
@

Next we define the CPU and its ALU:

@
cpu :: Vec 7 Value          -- ^ Register bank
    -> (Value,Instruction)  -- ^ (Memory output, Current instruction)
    -> ( Vec 7 Value
       , (MemAddr, Maybe (MemAddr,Value), InstrAddr)
       )
cpu regbank (memOut,instr) = (regbank',(rdAddr,(,aluOut) '<$>' wrAddrM,fromIntegral ipntr))
  where
    -- Current instruction pointer
    ipntr = regbank '!!' PC

    -- Decoder
    (MachCode {..}) = case instr of
      Compute op rx ry res -> nullCode {inputX=rx,inputY=ry,result=res,aluCode=op}
      Branch cr a          -> nullCode {inputX=cr,jmpM=Just a}
      Jump a               -> nullCode {aluCode=Incr,jmpM=Just a}
      Load a r             -> nullCode {ldReg=r,rdAddr=a}
      Store r a            -> nullCode {inputX=r,wrAddrM=Just a}
      Nop                  -> nullCode

    -- ALU
    regX   = regbank '!!' inputX
    regY   = regbank '!!' inputY
    aluOut = alu aluCode regX regY

    -- next instruction
    nextPC = case jmpM of
               Just a | aluOut /= 0 -> ipntr + a
               _                    -> ipntr + 1

    -- update registers
    regbank' = 'replace' Zero   0
             $ 'replace' PC     nextPC
             $ 'replace' result aluOut
             $ 'replace' ldReg  memOut
             $ regbank

alu Add   x y = x + y
alu Sub   x y = x - y
alu Incr  x _ = x + 1
alu Imm   x _ = x
alu CmpGt x y = if x > y then 1 else 0
@

We initially create a memory out of simple registers:

@
dataMem :: HiddenClockReset domain
        => Signal domain MemAddr                 -- ^ Read address
        -> Signal domain (Maybe (MemAddr,Value)) -- ^ (write address, data in)
        -> Signal domain Value                   -- ^ data out
dataMem rd wrM = 'Clash.Prelude.Mealy.mealy' dataMemT ('replicate' d32 0) (bundle (rd,wrM))
  where
    dataMemT mem (rd,wrM) = (mem',dout)
      where
        dout = mem '!!' rd
        mem' = case wrM of
                 Just (wr,din) -> 'replace' wr din mem
                 _ -> mem
@

And then connect everything:

@
system :: (KnownNat n, HiddenClockReset domain) => Vec n Instruction -> Signal domain Value
system instrs = memOut
  where
    memOut = dataMem rdAddr dout
    (rdAddr,dout,ipntr) = 'Clash.Prelude.Mealy.mealyB' cpu ('replicate' d7 0) (memOut,instr)
    instr  = 'Clash.Prelude.ROM.asyncRom' instrs '<$>' ipntr
@

Create a simple program that calculates the GCD of 4 and 6:

@
-- Compute GCD of 4 and 6
prog = -- 0 := 4
       Compute Incr Zero RegA RegA :>
       replicate d3 (Compute Incr RegA Zero RegA) ++
       Store RegA 0 :>
       -- 1 := 6
       Compute Incr Zero RegA RegA :>
       replicate d5 (Compute Incr RegA Zero RegA) ++
       Store RegA 1 :>
       -- A := 4
       Load 0 RegA :>
       -- B := 6
       Load 1 RegB :>
       -- start
       Compute CmpGt RegA RegB RegC :>
       Branch RegC 4 :>
       Compute CmpGt RegB RegA RegC :>
       Branch RegC 4 :>
       Jump 5 :>
       -- (a > b)
       Compute Sub RegA RegB RegA :>
       Jump (-6) :>
       -- (b > a)
       Compute Sub RegB RegA RegB :>
       Jump (-8) :>
       -- end
       Store RegA 2 :>
       Load 2 RegC :>
       Nil
@

And test our system:

@
>>> sampleN 31 (system prog)
[0,0,0,0,0,4,4,4,4,4,4,4,4,6,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,2]

@

to see that our system indeed calculates that the GCD of 6 and 4 is 2.

=== Improvement 1: using @asyncRam@

As you can see, it's fairly straightforward to build a memory using registers
and read ('!!') and write ('replace') logic. This might however not result in
the most efficient hardware structure, especially when building an ASIC.

Instead it is preferable to use the 'Clash.Prelude.RAM.asyncRam' function which
has the potential to be translated to a more efficient structure:

@
system2 :: (KnownNat n, HiddenClockReset domain) => Vec n Instruction -> Signal domain Value
system2 instrs = memOut
  where
    memOut = 'Clash.Prelude.RAM.asyncRam' d32 rdAddr dout
    (rdAddr,dout,ipntr) = 'mealyB' cpu ('replicate' d7 0) (memOut,instr)
    instr  = 'Clash.Prelude.ROM.asyncRom' instrs '<$>' ipntr
@

Again, we can simulate our system and see that it works. This time however,
we need to disregard the first few output samples, because the initial content of an
'Clash.Prelude.RAM.asyncRam' is 'undefined', and consequently, the first few
output samples are also 'undefined'. We use the utility function 'printX' to conveniently
filter out the undefinedness and replace it with the string "X" in the few leading outputs.

@
>>> printX $ sampleN 31 (system2 prog)
[X,X,X,X,X,4,4,4,4,4,4,4,4,6,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,2]

@

=== Improvement 2: using @blockRam@

Finally we get to using 'blockRam'. On FPGAs, 'Clash.Prelude.RAM.asyncRam' will
be implemented in terms of LUTs, and therefore take up logic resources. FPGAs
also have large(r) memory structures called /Block RAMs/, which are preferred,
especially as the memories we need for our application get bigger. The
'blockRam' function will be translated to such a /Block RAM/.

One important aspect of Block RAMs have a /synchronous/ read port, meaning that,
unlike the behaviour of 'Clash.Prelude.RAM.asyncRam', given a read address @r@
at time @t@, the value @v@ in the RAM at address @r@ is only available at time
@t+1@.

For us that means we need to change the design of our CPU. Right now, upon a
load instruction we generate a read address for the memory, and the value at
that read address is immediately available to be put in the register bank.
Because we will be using a BlockRAM, the value is delayed until the next cycle.
We hence need to also delay the register address to which the memory address
is loaded:

@
cpu2 :: (Vec 7 Value,Reg)    -- ^ (Register bank, Load reg addr)
     -> (Value,Instruction)  -- ^ (Memory output, Current instruction)
     -> ( (Vec 7 Value,Reg)
        , (MemAddr, Maybe (MemAddr,Value), InstrAddr)
        )
cpu2 (regbank,ldRegD) (memOut,instr) = ((regbank',ldRegD'),(rdAddr,(,aluOut) '<$>' wrAddrM,fromIntegral ipntr))
  where
    -- Current instruction pointer
    ipntr = regbank '!!' PC

    -- Decoder
    (MachCode {..}) = case instr of
      Compute op rx ry res -> nullCode {inputX=rx,inputY=ry,result=res,aluCode=op}
      Branch cr a          -> nullCode {inputX=cr,jmpM=Just a}
      Jump a               -> nullCode {aluCode=Incr,jmpM=Just a}
      Load a r             -> nullCode {ldReg=r,rdAddr=a}
      Store r a            -> nullCode {inputX=r,wrAddrM=Just a}
      Nop                  -> nullCode

    -- ALU
    regX   = regbank '!!' inputX
    regY   = regbank '!!' inputY
    aluOut = alu aluCode regX regY

    -- next instruction
    nextPC = case jmpM of
               Just a | aluOut /= 0 -> ipntr + a
               _                    -> ipntr + 1

    -- update registers
    ldRegD'  = ldReg -- Delay the ldReg by 1 cycle
    regbank' = 'replace' Zero   0
             $ 'replace' PC     nextPC
             $ 'replace' result aluOut
             $ 'replace' ldRegD memOut
             $ regbank
@

We can now finally instantiate our system with a 'blockRam':

@
system3 :: (KnownNat n, HiddenClockReset domain) => Vec n Instruction -> Signal domain Value
system3 instrs = memOut
  where
    memOut = 'blockRam' (replicate d32 0) rdAddr dout
    (rdAddr,dout,ipntr) = 'mealyB' cpu2 (('replicate' d7 0),Zero) (memOut,instr)
    instr  = 'Clash.Prelude.ROM.asyncRom' instrs '<$>' ipntr
@

We are, however, not done. We will also need to update our program. The reason
being that values that we try to load in our registers won't be loaded into the
register until the next cycle. This is a problem when the next instruction
immediately depended on this memory value. In our case, this was only the case
when the loaded the value @6@, which was stored at address @1@, into @RegB@.
Our updated program is thus:

@
prog2 = -- 0 := 4
       Compute Incr Zero RegA RegA :>
       replicate d3 (Compute Incr RegA Zero RegA) ++
       Store RegA 0 :>
       -- 1 := 6
       Compute Incr Zero RegA RegA :>
       replicate d5 (Compute Incr RegA Zero RegA) ++
       Store RegA 1 :>
       -- A := 4
       Load 0 RegA :>
       -- B := 6
       Load 1 RegB :>
       Nop :> -- Extra NOP
       -- start
       Compute CmpGt RegA RegB RegC :>
       Branch RegC 4 :>
       Compute CmpGt RegB RegA RegC :>
       Branch RegC 4 :>
       Jump 5 :>
       -- (a > b)
       Compute Sub RegA RegB RegA :>
       Jump (-6) :>
       -- (b > a)
       Compute Sub RegB RegA RegB :>
       Jump (-8) :>
       -- end
       Store RegA 2 :>
       Load 2 RegC :>
       Nil
@

When we simulate our system we see that it works. This time again,
we need to disregard the first sample, because the initial output of a
'blockRam' is 'undefined'. We use the utility function 'printX' to conveniently
filter out the undefinedness and replace it with the string "X".

@
>>> printX $ sampleN 33 (system3 prog2)
[X,0,0,0,0,0,4,4,4,4,4,4,4,4,6,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,2]

@

This concludes the short introduction to using 'blockRam'.

-}

{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

{-# LANGUAGE Safe #-}

{-# OPTIONS_HADDOCK show-extensions #-}

module Clash.Prelude.BlockRam
  ( -- * BlockRAM synchronised to the system clock
    blockRam
  , blockRamPow2
    -- * Read/Write conflict resolution
  , readNew
  )
where

import           GHC.TypeLits            (KnownNat, type (^))
import           GHC.Stack               (HasCallStack, withFrozenCallStack)

import qualified Clash.Explicit.BlockRam as E
import           Clash.Signal
import           Clash.Sized.Unsigned    (Unsigned)
import           Clash.Sized.Vector      (Vec)

{- $setup
>>> import Clash.Prelude as C
>>> import qualified Data.List as L
>>> :set -XDataKinds -XRecordWildCards -XTupleSections -XTypeApplications -XFlexibleContexts
>>> type InstrAddr = Unsigned 8
>>> type MemAddr = Unsigned 5
>>> type Value = Signed 8
>>> :{
data Reg
  = Zero
  | PC
  | RegA
  | RegB
  | RegC
  | RegD
  | RegE
  deriving (Eq,Show,Enum)
:}

>>> :{
data Operator = Add | Sub | Incr | Imm | CmpGt
  deriving (Eq,Show)
:}

>>> :{
data Instruction
  = Compute Operator Reg Reg Reg
  | Branch Reg Value
  | Jump Value
  | Load MemAddr Reg
  | Store Reg MemAddr
  | Nop
  deriving (Eq,Show)
:}

>>> :{
data MachCode
  = MachCode
  { inputX  :: Reg
  , inputY  :: Reg
  , result  :: Reg
  , aluCode :: Operator
  , ldReg   :: Reg
  , rdAddr  :: MemAddr
  , wrAddrM :: Maybe MemAddr
  , jmpM    :: Maybe Value
  }
:}

>>> :{
nullCode = MachCode { inputX = Zero, inputY = Zero, result = Zero, aluCode = Imm
                    , ldReg = Zero, rdAddr = 0, wrAddrM = Nothing
                    , jmpM = Nothing
                    }
:}

>>> :{
alu Add   x y = x + y
alu Sub   x y = x - y
alu Incr  x _ = x + 1
alu Imm   x _ = x
alu CmpGt x y = if x > y then 1 else 0
:}

>>> :{
cpu :: Vec 7 Value          -- ^ Register bank
    -> (Value,Instruction)  -- ^ (Memory output, Current instruction)
    -> ( Vec 7 Value
       , (MemAddr,Maybe (MemAddr,Value),InstrAddr)
       )
cpu regbank (memOut,instr) = (regbank',(rdAddr,(,aluOut) <$> wrAddrM,fromIntegral ipntr))
  where
    -- Current instruction pointer
    ipntr = regbank C.!! PC
    -- Decoder
    (MachCode {..}) = case instr of
      Compute op rx ry res -> nullCode {inputX=rx,inputY=ry,result=res,aluCode=op}
      Branch cr a          -> nullCode {inputX=cr,jmpM=Just a}
      Jump a               -> nullCode {aluCode=Incr,jmpM=Just a}
      Load a r             -> nullCode {ldReg=r,rdAddr=a}
      Store r a            -> nullCode {inputX=r,wrAddrM=Just a}
      Nop                  -> nullCode
    -- ALU
    regX   = regbank C.!! inputX
    regY   = regbank C.!! inputY
    aluOut = alu aluCode regX regY
    -- next instruction
    nextPC = case jmpM of
               Just a | aluOut /= 0 -> ipntr + a
               _                    -> ipntr + 1
    -- update registers
    regbank' = replace Zero   0
             $ replace PC     nextPC
             $ replace result aluOut
             $ replace ldReg  memOut
             $ regbank
:}

>>> :{
dataMem
  :: HiddenClockReset domain
  => Signal domain MemAddr
  -> Signal domain (Maybe (MemAddr,Value))
  -> Signal domain Value
dataMem rd wrM = mealy dataMemT (C.replicate d32 0) (bundle (rd,wrM))
  where
    dataMemT mem (rd,wrM) = (mem',dout)
      where
        dout = mem C.!! rd
        mem' = case wrM of
                 Just (wr,din) -> replace wr din mem
                 Nothing       -> mem
:}

>>> :{
system
  :: (KnownNat n, HiddenClockReset domain)
  => Vec n Instruction
  -> Signal domain Value
system instrs = memOut
  where
    memOut = dataMem rdAddr dout
    (rdAddr,dout,ipntr) = mealyB cpu (C.replicate d7 0) (memOut,instr)
    instr  = asyncRom instrs <$> ipntr
:}

>>> :{
-- Compute GCD of 4 and 6
prog = -- 0 := 4
       Compute Incr Zero RegA RegA :>
       C.replicate d3 (Compute Incr RegA Zero RegA) C.++
       Store RegA 0 :>
       -- 1 := 6
       Compute Incr Zero RegA RegA :>
       C.replicate d5 (Compute Incr RegA Zero RegA) C.++
       Store RegA 1 :>
       -- A := 4
       Load 0 RegA :>
       -- B := 6
       Load 1 RegB :>
       -- start
       Compute CmpGt RegA RegB RegC :>
       Branch RegC 4 :>
       Compute CmpGt RegB RegA RegC :>
       Branch RegC 4 :>
       Jump 5 :>
       -- (a > b)
       Compute Sub RegA RegB RegA :>
       Jump (-6) :>
       -- (b > a)
       Compute Sub RegB RegA RegB :>
       Jump (-8) :>
       -- end
       Store RegA 2 :>
       Load 2 RegC :>
       Nil
:}

>>> :{
system2
  :: (KnownNat n, HiddenClockReset domain)
  => Vec n Instruction
  -> Signal domain Value
system2 instrs = memOut
  where
    memOut = asyncRam d32 rdAddr dout
    (rdAddr,dout,ipntr) = mealyB cpu (C.replicate d7 0) (memOut,instr)
    instr  = asyncRom instrs <$> ipntr
:}

>>> :{
cpu2 :: (Vec 7 Value,Reg)    -- ^ (Register bank, Load reg addr)
     -> (Value,Instruction)  -- ^ (Memory output, Current instruction)
     -> ( (Vec 7 Value,Reg)
        , (MemAddr,Maybe (MemAddr,Value),InstrAddr)
        )
cpu2 (regbank,ldRegD) (memOut,instr) = ((regbank',ldRegD'),(rdAddr,(,aluOut) <$> wrAddrM,fromIntegral ipntr))
  where
    -- Current instruction pointer
    ipntr = regbank C.!! PC
    -- Decoder
    (MachCode {..}) = case instr of
      Compute op rx ry res -> nullCode {inputX=rx,inputY=ry,result=res,aluCode=op}
      Branch cr a          -> nullCode {inputX=cr,jmpM=Just a}
      Jump a               -> nullCode {aluCode=Incr,jmpM=Just a}
      Load a r             -> nullCode {ldReg=r,rdAddr=a}
      Store r a            -> nullCode {inputX=r,wrAddrM=Just a}
      Nop                  -> nullCode
    -- ALU
    regX   = regbank C.!! inputX
    regY   = regbank C.!! inputY
    aluOut = alu aluCode regX regY
    -- next instruction
    nextPC = case jmpM of
               Just a | aluOut /= 0 -> ipntr + a
               _                    -> ipntr + 1
    -- update registers
    ldRegD'  = ldReg -- Delay the ldReg by 1 cycle
    regbank' = replace Zero   0
             $ replace PC     nextPC
             $ replace result aluOut
             $ replace ldRegD memOut
             $ regbank
:}

>>> :{
system3
  :: (KnownNat n, HiddenClockReset domain)
  => Vec n Instruction
  -> Signal domain Value
system3 instrs = memOut
  where
    memOut = blockRam (C.replicate d32 0) rdAddr dout
    (rdAddr,dout,ipntr) = mealyB cpu2 ((C.replicate d7 0),Zero) (memOut,instr)
    instr  = asyncRom instrs <$> ipntr
:}

>>> :{
prog2 = -- 0 := 4
       Compute Incr Zero RegA RegA :>
       C.replicate d3 (Compute Incr RegA Zero RegA) C.++
       Store RegA 0 :>
       -- 1 := 6
       Compute Incr Zero RegA RegA :>
       C.replicate d5 (Compute Incr RegA Zero RegA) C.++
       Store RegA 1 :>
       -- A := 4
       Load 0 RegA :>
       -- B := 6
       Load 1 RegB :>
       Nop :> -- Extra NOP
       -- start
       Compute CmpGt RegA RegB RegC :>
       Branch RegC 4 :>
       Compute CmpGt RegB RegA RegC :>
       Branch RegC 4 :>
       Jump 5 :>
       -- (a > b)
       Compute Sub RegA RegB RegA :>
       Jump (-6) :>
       -- (b > a)
       Compute Sub RegB RegA RegB :>
       Jump (-8) :>
       -- end
       Store RegA 2 :>
       Load 2 RegC :>
       Nil
:}

-}

-- | Create a blockRAM with space for @n@ elements.
--
-- * __NB__: Read value is delayed by 1 cycle
-- * __NB__: Initial output value is 'undefined'
--
-- @
-- bram40
--   :: 'HiddenClock' domain
--   => 'Signal' domain ('Unsigned' 6)
--   -> 'Signal' domain (Maybe ('Unsigned' 6, 'Clash.Sized.BitVector.Bit'))
--   -> 'Signal' domain 'Clash.Sized.BitVector.Bit'
-- bram40 = 'blockRam' ('Clash.Sized.Vector.replicate' d40 1)
-- @
--
-- Additional helpful information:
--
-- * See "Clash.Prelude.BlockRam#usingrams" for more information on how to use a
-- Block RAM.
-- * Use the adapter 'readNew' for obtaining write-before-read semantics like this: @readNew (blockRam inits) rd wrM@.
blockRam
  :: (Enum addr, HiddenClock domain, HasCallStack)
  => Vec n a     -- ^ Initial content of the BRAM, also
                 -- determines the size, @n@, of the BRAM.
                 --
                 -- __NB__: __MUST__ be a constant.
  -> Signal domain addr -- ^ Read address @r@
  -> Signal domain (Maybe (addr, a))
   -- ^ (write address @w@, value to write)
  -> Signal domain a
  -- ^ Value of the @blockRAM@ at address @r@ from the previous clock
  -- cycle
blockRam = \cnt rd wrM -> withFrozenCallStack
  (hideClock E.blockRam cnt rd wrM)
{-# INLINE blockRam #-}

-- | Create a blockRAM with space for 2^@n@ elements
--
-- * __NB__: Read value is delayed by 1 cycle
-- * __NB__: Initial output value is 'undefined'
--
-- @
-- bram32
--   :: 'HiddenClock' domain
--   => 'Signal' domain ('Unsigned' 5)
--   -> 'Signal' domain (Maybe ('Unsigned' 5, 'Clash.Sized.BitVector.Bit'))
--   -> 'Signal' domain 'Clash.Sized.BitVector.Bit'
-- bram32 = 'blockRamPow2' ('Clash.Sized.Vector.replicate' d32 1)
-- @
--
-- Additional helpful information:
--
-- * See "Clash.Prelude.BlockRam#usingrams" for more information on how to use a
-- Block RAM.
-- * Use the adapter 'readNew' for obtaining write-before-read semantics like this: @readNew (blockRamPow2 inits) rd wrM@.
blockRamPow2
  :: (KnownNat n, HiddenClock domain, HasCallStack)
  => Vec (2^n) a         -- ^ Initial content of the BRAM, also
                         -- determines the size, @2^n@, of the BRAM.
                         --
                         -- __NB__: __MUST__ be a constant.
  -> Signal domain (Unsigned n) -- ^ Read address @r@
  -> Signal domain (Maybe (Unsigned n, a))
  -- ^ (write address @w@, value to write)
  -> Signal domain a
  -- ^ Value of the @blockRAM@ at address @r@ from the previous clock
  -- cycle
blockRamPow2 = \cnt rd wrM -> withFrozenCallStack
  (hideClock E.blockRamPow2 cnt rd wrM)
{-# INLINE blockRamPow2 #-}

-- | Create read-after-write blockRAM from a read-before-write one (synchronised to system clock)
--
-- >>> import Clash.Prelude
-- >>> :t readNew (blockRam (0 :> 1 :> Nil))
-- readNew (blockRam (0 :> 1 :> Nil))
--   :: ...
--      ... =>
--      Signal domain addr
--      -> Signal domain (Maybe (addr, a)) -> Signal domain a
readNew :: (Eq addr, HiddenClockReset domain)
        => (Signal domain addr -> Signal domain (Maybe (addr, a)) -> Signal domain a)
        -- ^ The @ram@ component
        -> Signal domain addr              -- ^ Read address @r@
        -> Signal domain (Maybe (addr, a)) -- ^ (Write address @w@, value to write)
        -> Signal domain a
        -- ^ Value of the @ram@ at address @r@ from the previous clock
        -- cycle
readNew = hideClockReset (\clk rst -> E.readNew rst clk)
{-# INLINE readNew #-}
