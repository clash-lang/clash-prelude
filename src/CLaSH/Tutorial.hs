{-|
Copyright : © 2014-2016, Christiaan Baaij, 2017, QBayLogic
Licence   : Creative Commons 4.0 (CC BY 4.0) (http://creativecommons.org/licenses/by/4.0/)
-}

{-# LANGUAGE NoImplicitPrelude, MagicHash #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module CLaSH.Tutorial (
  -- * Introduction
  -- $introduction

  -- * Installation
  -- $installation

  -- * Working with this tutorial
  -- $working

  -- * Your first circuit
  -- $mac_example

  -- *** Sequential circuit
  -- $mac2

  -- *** Generating VHDL
  -- $mac3

  -- *** Circuit testbench
  -- $mac4

  -- *** Generating Verilog and SystemVerilog
  -- $mac5

  -- *** Alternative specifications
  -- $mac6

  -- * Higher-order functions
  -- $higher_order

  -- * Composition of sequential circuits
  -- $composition_sequential

  -- * TopEntity annotations: controlling the VHDL\/(System)Verilog generation.
  -- $annotations

  -- * Multiple clock domains
  -- $multiclock

  -- * Advanced: Primitives
  -- $primitives

  -- *** Verilog primitives
  -- $vprimitives

  -- *** SystemVerilog primitives
  -- $svprimitives

  -- * Conclusion
  -- $conclusion

  -- * Troubleshooting
  -- $errorsandsolutions

  -- * Limitations of CλaSH
  -- $limitations

  -- * CλaSH vs Lava
  -- $vslava
  )
where

import CLaSH.Prelude
import CLaSH.Prelude.Explicit
import CLaSH.Prelude.BlockRam
import Control.Monad.ST
import Data.Array
import Data.Char
import Data.Int
import GHC.Prim
import GHC.TypeLits
import GHC.Word
import Data.Default

{- $setup
>>> :set -XTemplateHaskell
>>> :set -XDataKinds
>>> let ma acc (x,y) = acc + x * y
>>> :{
let macT acc (x,y) = (acc',o)
       where
         acc' = ma acc (x,y)
         o    = acc
:}

>>> :set -XFlexibleContexts
>>> :set -fplugin GHC.TypeLits.Normalise
>>> let compareSwapL a b = if a < b then (a,b) else (b,a)
>>> :{
let sortV xs = map fst sorted :< (snd (last sorted))
      where
        lefts  = head xs :> map snd (init sorted)
        rights = tail xs
        sorted = zipWith compareSwapL lefts rights
:}

>>> :{
let sortVL xs = map fst sorted :< (snd (last sorted))
      where
        lefts  = head xs :> map snd (init sorted)
        rights = tail xs
        sorted = zipWith compareSwapL (lazyV lefts) rights
:}

>>> let mac = mealy macT 0
>>> let topEntity = mac :: Signal (Signed 9, Signed 9) -> Signal (Signed 9)
>>> let testInput = stimuliGenerator $(listToVecTH [(1,1) :: (Signed 9,Signed 9),(2,2),(3,3),(4,4)])
>>> let expectedOutput = outputVerifier $(listToVecTH [0 :: Signed 9,1,5,14])
>>> :{
let fibR :: Unsigned 64 -> Unsigned 64
    fibR 0 = 0
    fibR 1 = 1
    fibR n = fibR (n-1) + fibR (n-2)
:}

>>> :{
let fibS :: Signal (Unsigned 64)
    fibS = r
      where r = register 0 r + register 0 (register 1 r)
:}

-}

{- $introduction
CλaSH (pronounced ‘clash’) is a functional hardware description language that
borrows both its syntax and semantics from the functional programming language
Haskell. It provides a familiar structural design approach to both combination
and synchronous sequential circuits. The CλaSH compiler transforms these
high-level descriptions to low-level synthesizable VHDL, Verilog, or
SystemVerilog.

Features of CλaSH:

  * Strongly typed, but with a very high degree of type inference, enabling
    both safe and fast prototyping using concise descriptions.
  * Interactive REPL: load your designs in an interpreter and easily test all
    your component without needing to setup a test bench.
  * Compile your designs for fast simulation.
  * Higher-order functions, in combination with type inference, result in
    designs that are fully parametric by default.
  * Synchronous sequential circuit design based on streams of values, called
    @Signal@s, lead to natural descriptions of feedback loops.
  * Multiple clock domains, with type safe clock domain crossing.
  * Template language for introducing new VHDL/(System)Verilog primitives.

Although we say that CλaSH borrows the semantics of Haskell, that statement
should be taken with a grain of salt. What we mean to say is that the CλaSH
compiler views a circuit description as /structural/ description. This means,
in an academic handwavy way, that every function denotes a component and every
function application denotes an instantiation of said component. Now, this has
consequences on how we view /recursively/ defined functions: structurally, a
recursively defined function would denote an /infinitely/ deep / structured
component, something that cannot be turned into an actual circuit
(See also <#limitations Limitations of CλaSH>).

On the other hand, Haskell's by-default non-strict evaluation works very well
for the simulation of the feedback loops, which are ubiquitous in digital
circuits. That is, when we take our structural view to circuit descriptions,
value-recursion corresponds directly to a feedback loop:

@
counter = s
  where
    s = 'register' 0 (s + 1)
@

The above definition, which uses value-recursion, /can/ be synthesized to a
circuit by the CλaSH compiler.

Over time, you will get a better feeling for the consequences of taking a
/structural/ view on circuit descriptions. What is always important to
remember is that every applied functions results in an instantiated component,
and also that the compiler will /never/ infer / invent more logic than what is
specified in the circuit description.

With that out of the way, let us continue with installing CλaSH and building
our first circuit.
-}

{- $installation
The CλaSH compiler and Prelude library for circuit design only work with the
<http://haskell.org/ghc GHC> Haskell compiler version 8.0 (lower versions of
GHC are not supported).

  (1) Install __GHC 8.0__

      * Download and install <https://www.haskell.org/ghc/download_ghc_8_0_2 GHC for your platform>.
        Unix user can use @./configure prefix=\<LOCATION\>@ to set the installation
        location.

      * Make sure that the @bin@ directory of __GHC__ is in your @PATH@.

    In case you cannot find what you are looking for on <https://www.haskell.org/ghc/download_ghc_8_0_2>,
    you can, /alternatively/, use the following instructions:

      * Ubuntu:

          * Run: @sudo add-apt-repository -y ppa:hvr/ghc@
          * Run: @sudo apt-get update@
          * Run: @sudo apt-get install cabal-install-1.24 ghc-8.0.2 libtinfo-dev@
          * Update your @PATH@ with: @\/opt\/ghc\/8.0.2\/bin@, @\/opt\/cabal\/1.24/bin@, and @\$HOME\/.cabal\/bin@
          * Run: @cabal update@
          * Skip step 2.

      * OS X:

          * Follow the instructions on: <https://www.haskell.org/platform/mac.html Haskell Platform Mac OS X>
            to install the /minimal/ Haskell platform
          * Run: @cabal update@
          * Skip step 2.

      * Windows:

          * Follow the instructions on: <https://www.haskell.org/platform/windows.html Haskell Platform Windows>
            to install the /minimal/ Haskell platform
          * Run: @cabal update@
          * Skip step 2.

  (2) Install __Cabal (version 1.24 or higher)__

      * Binary, when available:

          * Download the binary for <http://www.haskell.org/cabal/download.html cabal-install>
          * Put the binary in a location mentioned in your @PATH@
          * Add @cabal@'s @bin@ directory to your @PATH@:

              * Windows: @%appdata%\\cabal\\bin@
              * Unix: @\$HOME\/.cabal\/bin@

      * Source:

          * Download the sources for <http://hackage.haskell.org/package/cabal-install cabal-install>
          * Unpack (@tar xf@) the archive and @cd@ to the directory
          * Run: @sh bootstrap.sh@
          * Follow the instructions to add @cabal@ to your @PATH@

      * Run @cabal update@

  (2) Install __CλaSH__

      * Run:

          * /i386/ Linux: @cabal install clash-ghc --enable-documentation --enable-executable-dynamic@
          * Other: @cabal install clash-ghc --enable-documentation@

      * /This is going to take awhile, so have a refreshment/

  (4) Verify that everything is working by:

      * Downloading the <https://raw.githubusercontent.com/clash-lang/clash-compiler/049e6e2eacb9b3b5ae8664b9b79979c321b322d9/examples/FIR.hs Fir.hs> example
      * Run: @clash --interactive FIR.hs@
      * Execute, in the interpreter, the @:vhdl@ command
      * Execute, in the interpreter, the @:verilog@ command
      * Execute, in the interpreter, the @:systemverilog@ command
      * Exit the interpreter using @:q@
      * Examine the VHDL code in the @vhdl@ directory
      * Examine the Verilog code in the @verilog@ directory
      * Examine the SystemVerilog code in the @systemverilog@ directory

-}

{- $working
This tutorial can be followed best whilst having the CλaSH interpreter running
at the same time. If you followed the installation instructions, you already
know how to start the CλaSH compiler in interpretive mode:

@
clash --interactive
@

For those familiar with Haskell/GHC, this is indeed just @GHCi@, with three
added commands (@:vhdl@, @:verilog@, and @:systemverilog@). You can load files
into the interpreter using the @:l \<FILENAME\>@ command. Now, depending on your
choice in editor, the following @edit-load-run@ cycle probably work best for you:

  * __Commandline (e.g. emacs, vim):__

      * You can run system commands using @:!@, for example @:! touch \<FILENAME\>@
      * Set the /editor/ mode to your favourite editor using: @:set editor \<EDITOR\>@
      * You can load files using @:l@ as noted above.
      * You can go into /editor/ mode using: @:e@
      * Leave the editor mode by quitting the editor (e.g. @:wq@ in @vim@)

  * __GUI (e.g. SublimeText, Notepad++):__

      * Just create new files in your editor.
      * Load the files using @:l@ as noted above.
      * Once a file has been edited and saved, type @:r@ to reload the files in
        the interpreter

You are of course free to deviate from these suggestions as you see fit :-) It
is just recommended that you have the CλaSH interpreter open during this
tutorial.
-}

{- $mac_example
The very first circuit that we will build is the \"classic\" multiply-and-accumulate
(MAC) circuit. This circuit is as simple as it sounds, it multiplies its inputs
and accumulates them. Before we describe any logic, we must first create the
file we will be working on and input some preliminaries:

* Create the file:

    @
    MAC.hs
    @

* Write on the first line the module header:

    @
    module MAC where
    @

    Module names must always start with a __C__apital letter. Also make sure that
    the file name corresponds to the module name.

* Add the import statement for the CλaSH prelude library:

    @
    import CLaSH.Prelude
    @

    This imports all the necessary functions and datatypes for circuit description.

We can now finally start describing the logic of our circuit, starting with just
the multiplication and addition:

@
ma acc (x,y) = acc + x * y
@

If you followed the instructions of running the interpreter side-by-side, you
can already test this function:

>>> ma 4 (8,9)
76
>>> ma 2 (3,4)
14

We can also examine the inferred type of @ma@ in the interpreter:

>>> :t ma
ma :: Num a => a -> (a, a) -> a

Talking about /types/ also brings us to one of the most important parts of this
tutorial: /types/ and /synchronous sequential logic/. Especially how we can
always determine, through the types of a specification, if it describes
combinational logic or (synchronous) sequential logic. We do this by examining
the type of one of the sequential primitives, the @'register'@ function:

@
register :: a -> 'Signal' a -> 'Signal' a
register i s = ...
@

Where we see that the second argument and the result are not just of the
/polymorphic/ @a@ type, but of the type: @'Signal' a@. All (synchronous)
sequential circuits work on values of type @'Signal' a@. Combinational
circuits always work on values of, well, not of type @'Signal' a@. A 'Signal'
is an (infinite) list of samples, where the samples correspond to the values
of the 'Signal' at discrete, consecutive, ticks of the /clock/. All (sequential)
components in the circuit are synchronized to this global /clock/. For the
rest of this tutorial, and probably at any moment where you will be working with
CλaSH, you should probably not actively think about 'Signal's as infinite lists
of samples, but just as values that are manipulated by sequential circuits. To
make this even easier, it actually not possible to manipulate the underlying
representation directly: you can only modify 'Signal' values through a set of
primitives such as the 'register' function above.

Now, let us get back to the functionality of the 'register' function: it is
a simple @latch@ that only changes state at the tick of the global /clock/, and
it has an initial value @a@ which is its output at time 0. We can further
examine the 'register' function by taking a look at the first 4 samples of the
'register' functions applied to a constant signal with the value 8:

>>> sampleN 4 (register 0 (signal 8))
[0,8,8,8]

Where we see that the initial value of the signal is the specified 0 value,
followed by 8's.
-}

{- $mac2
The 'register' function is our primary sequential building block to capture
/state/. It is used internally by one of the "CLaSH.Prelude" function that we
will use to describe our MAC circuit. Note that the following paragraphs will
only show one of many ways to specify a sequential circuit, at the section we
will show a couple more.

A principled way to describe a sequential circuit is to use one of the classic
machine models, within the CλaSH prelude library offer standard function to
support the <http://en.wikipedia.org/wiki/Mealy_machine Mealy machine>.
To improve sharing, we will combine the transition function and output function
into one. This gives rise to the following Mealy specification of the MAC
circuit:

@
macT acc (x,y) = (acc',o)
  where
    acc' = ma acc (x,y)
    o    = acc
@

Note that the @where@ clause and explicit tuple are just for demonstrative
purposes, without loss of sharing we could've also written:

@
macT acc inp = (ma acc inp,acc)
@

Going back to the original specification we note the following:

  * 'acc' is the current /state/ of the circuit.
  * '(x,y)' is its input.
  * 'acc'' is the updated, or next, /state/.
  * 'o' is the output.

When we examine the type of 'macT' we see that is still completely combinational:

>>> :t macT
macT :: Num t => t -> (t, t) -> (t, t)

The "CLaSH.Prelude" library contains a function that creates a sequential
circuit from a combinational circuit that has the same Mealy machine type /
shape of @macT@:

@
mealy :: (s -> i -> (s,o))
      -> s
      -> ('Signal' i -> 'Signal' o)
mealy f initS = ...
@

The complete sequential MAC circuit can now be specified as:

@
mac = 'mealy' macT 0
@

Where the first argument of @'mealy'@ is our @macT@ function, and the second
argument is the initial state, in this case 0. We can see it is functioning
correctly in our interpreter:

>>> import qualified Data.List as L
>>> L.take 4 $ simulate mac [(1,1),(2,2),(3,3),(4,4)]
[0,1,5,14]

Where we simulate our sequential circuit over a list of input samples and take
the first 4 output samples. We have now completed our first sequential circuit
and have made an initial confirmation that it is working as expected.
-}

{- $mac3
We are now almost at the point that we can create actual hardware, in the form
of a <http://en.wikipedia.org/wiki/VHDL VHDL> netlist, from our sequential
circuit specification. The first thing we have to do is create a function
called 'topEntity' and ensure that it has a __monomorphic__ type. In our case
that means that we have to give it an explicit type annotation. It might not
always be needed, you can always check the type with the @:t@ command and see
if the function is monomorphic:

@
topEntity :: 'Signal' ('Signed' 9, 'Signed' 9) -> 'Signal' ('Signed' 9)
topEntity = mac
@

Which makes our circuit work on 9-bit signed integers. Including the above
definition, our complete @MAC.hs@ should now have the following content:

@
module MAC where

import CLaSH.Prelude

ma acc (x,y) = acc + x * y

macT acc (x,y) = (acc',o)
  where
    acc' = ma acc (x,y)
    o    = acc

mac = 'mealy' macT 0

topEntity :: 'Signal' ('Signed' 9, 'Signed' 9) -> 'Signal' ('Signed' 9)
topEntity = mac
@

The 'topEntity' function is the starting point for the CλaSH compiler to
transform your circuit description into a VHDL netlist. It must meet the
following restrictions in order for the CλaSH compiler to work:

  * It must be completely monomorphic
  * It must be completely first-order

Our 'topEntity' meets those restrictions, and so we can convert it successfully
to VHDL by executing the @:vhdl@ command in the interpreter. This will create
a directory called 'vhdl', which contains a directory called @MAC@, which
ultimately contains all the generated VHDL files. You can now load these files
into your favourite VHDL synthesis tool, marking @MAC_topEntity.vhdl@ as the file
containing the top level entity.
-}

{- $mac4
There are multiple reasons as to why might you want to create a so-called
/testbench/ for the VHDL:

  * You want to compare post-synthesis / post-place&route behaviour to that of
    the behaviour of the original VHDL.
  * Need representative stimuli for your dynamic power calculations
  * Verify that the VHDL output of the CλaSH compiler has the same behaviour as
    the Haskell / CλaSH specification.

For these purposes, you can have CλaSH compiler generate a @MAC_testbench.vhdl@
file which contains a stimulus generator and an expected output verifier. The
CλaSH compiler looks for the following functions to generate these to aspects:

  1. @testInput@ for the stimulus generator.
  2. @expectedOutput@ for the output verification.

Given a @topEntity@ with the type:

@
__topEntity__ :: 'Signal' a -> 'Signal' b
@

Where @a@ and @b@ are placeholders for monomorphic types: the 'topEntity' is
not allowed to be polymorphic. So given the above type for the 'topEntity', the
type of 'testInput' should be:

@
__testInput__ :: 'Signal' a
@

And the type of @expectedOutput@ should be:

@
__expectedOutput__ :: 'Signal' b -> 'Signal' Bool
@

Where the 'expectedOutput' function should assert to 'True' once it has verified
all expected values. The "CLaSH.Prelude" module contains two standard functions
to serve the above purpose, but a user is free to use any CλaSH specification
to describe these two functions. For this tutorial we will be using the
functions specified in the "CLaSH.Prelude" module, which are @'stimuliGenerator'@
and @'outputVerifier'@:

@
testInput :: 'Signal' ('Signed' 9,'Signed' 9)
testInput = 'stimuliGenerator' $('listToVecTH' [(1,1) :: ('Signed' 9,'Signed' 9),(2,2),(3,3),(4,4)])

expectedOutput :: 'Signal' ('Signed' 9) -> 'Signal' Bool
expectedOutput = 'outputVerifier' $('listToVecTH' [0 :: 'Signed' 9,1,5,14])
@

This will create a stimulus generator that creates the same inputs as we used
earlier for the simulation of the circuit, and creates an output verifier that
compares against the results we got from our earlier simulation. We can even
simulate the behaviour of the /testbench/:

>>> sampleN 7 $ expectedOutput (topEntity testInput)
[False,False,False,False
cycle(system1000): 4, outputVerifier
expected value: 14, not equal to actual value: 30
,True
cycle(system1000): 5, outputVerifier
expected value: 14, not equal to actual value: 46
,True
cycle(system1000): 6, outputVerifier
expected value: 14, not equal to actual value: 62
,True]

We can see that for the first 4 samples, everything is working as expected,
after which warnings are being reported. The reason is that 'stimuliGenerator'
will keep on producing the last sample, (4,4), while the 'outputVerifier' will
keep on expecting the last sample, 14. In the VHDL testbench these errors won't
show, as the the global clock will be stopped after 4 ticks.

You should now again run @:vhdl@ in the interpreter; this time the compiler
will take a bit longer to generate all the circuits. After it is finished you
can load all the files in your favourite VHDL simulation tool. Once all files
are loaded into the VHDL simulator, run the simulation on the @testbench@ entity.
On questasim / modelsim: doing a @run -all@ will finish once the output verifier
will assert its output to @true@. The generated testbench, modulo the clock
signal generator(s), is completely synthesizable. This means that if you want to
test your circuit on an FPGA, you will only have to replace the clock signal
generator(s) by actual clock sources, such as an onboard PLL.
-}

{- $mac5
Aside from being to generate VHDL, the CλaSH compiler can also generate Verilog
and SystemVerilog. You can repeat the previous two parts of the tutorial, but
instead of executing the @:vhdl@ command, you execute the @:verilog@ or
@:sytemverilog@ command in the interpreter. This will create a directory called
@verilog@, respectively @systemverilog@, which contains a directory called @MAC@,
which ultimately contains all the generated Verilog and SystemVerilog files.
Verilog files end in the file extension @v@, while SystemVerilog files end in
the file extension @sv@.

This concludes the main part of this section on \"Your first circuit\", read on
for alternative specifications for the same 'mac' circuit, or just skip to the
next section where we will describe another DSP classic: an FIR filter
structure.
-}

{- $mac6
* __'Num' instance for 'Signal'__:

    @'Signal' a@ is also also considered a 'Num'eric type as long as the value
    type /a/ is also 'Num'eric.  This means that we can also use the standard
    numeric operators, such as ('*') and ('+'), directly on signals. An
    alternative specification of the 'mac' circuit will also use the 'register'
    function directly:

    @
    macN (x,y) = acc
      where
        acc = 'register' 0 (acc + x * y)
    @

* __'Applicative' instance for 'Signal'__:

    We can also mix the combinational 'ma' function, with the sequential
    'register' function, by lifting the 'ma' function to the sequential 'Signal'
    domain using the operators ('<$>' and '<*>') of the 'Applicative' type
    class:

    @
    macA (x,y) = acc
      where
        acc  = 'register' 0 acc'
        acc' = ma '<$>' acc '<*>' 'bundle' (x,y)
    @

* __'Control.Monad.State.Lazy.State' Monad__

    We can also implement the original @macT@ function as a
    @'Control.Monad.State.Lazy.State'@
    monadic computation. First we must an extra import statement, right after
    the import of "CLaSH.Prelude":

    @
    import Control.Monad.State
    @

    We can then implement macT as follows:

    @
    macTS (x,y) = do
      acc <- 'Control.Monad.State.Lazy.get'
      'Control.Monad.State.Lazy.put' (acc + x * y)
      return acc
    @

    We can use the 'mealy' function again, although we will have to change
    position of the arguments and result:

    @
    asStateM :: (i -> 'Control.Monad.State.Lazy.State' s o)
             -> s
             -> ('Signal' i -> 'Signal' o)
    asStateM f i = 'mealy' g i
      where
        g s x = let (o,s') = 'Control.Monad.State.Lazy.runState' (f x) s
                in  (s',o)
    @

    We can then create the complete 'mac' circuit as:

    @
    macS = asStateM macTS 0
    @
-}

{- $higher_order
An FIR filter is defined as: the dot-product of a set of filter coefficients and
a window over the input, where the size of the window matches the number
of coefficients.

@
dotp as bs = 'sum' ('zipWith' (*) as bs)

fir coeffs x_t = y_t
  where
    y_t = dotp coeffs xs
    xs  = 'window' x_t

topEntity :: 'Signal' ('Signed' 16) -> 'Signal' ('Signed' 16)
topEntity = fir (0 ':>' 1 ':>' 2 ':>' 3 ':>' 'Nil')
@

Here we can see that, although the CλaSH compiler handles recursive function
definitions poorly, many of the regular patterns that we often encounter in
circuit design are already captured by the higher-order functions that are
present for the 'Vec'tor type.
-}

{- $composition_sequential
Given a function @f@ of type:

@
__f__ :: Int -> (Bool, Int) -> (Int, (Int, Bool))
@

When we want to make compositions of @f@ in @g@ using 'mealy', we have to
write:

@
g a b c = (b1,b2,i2)
  where
    (i1,b1) = 'unbundle' ('mealy' f 0 ('bundle' (a,b)))
    (i2,b2) = 'unbundle' ('mealy' f 3 ('bundle' (i1,c)))
@

Why do we need these 'bundle', and 'unbundle' functions you might ask? When we
look at the type of 'mealy':

@
__mealy__ :: (s -> i -> (s,o))
      -> s
      -> ('Signal' i -> 'Signal' o)
@

we see that the resulting function has an input of type @'Signal' i@, and an
output of @'Signal' o@. However, the type of @(a,b)@ in the definition of @g@ is:
@('Signal' Bool, 'Signal' Int)@. And the type of @(i1,b1)@ is of type
@('Signal' Int, 'Signal' Bool)@.

Syntactically, @'Signal' (Bool,Int)@ and @('Signal' Bool, 'Signal' Int)@ are /unequal/.
So we need to make a conversion between the two, that is what 'bundle' and
'unbundle' are for. In the above case 'bundle' gets the type:

@
__bundle__ :: ('Signal' Bool, 'Signal' Int) -> 'Signal' (Bool,Int)
@

and 'unbundle':

@
__unbundle__ :: 'Signal' (Int,Bool) -> ('Signal' Int, 'Signal' Bool)
@

The /true/ types of these two functions are, however:

@
__bundle__   :: 'Bundle' a => 'Unbundled' a -> 'Signal' a
__unbundle__ :: 'Bundle' a => 'Signal' a -> 'Unbundled' a
@

'Unbundled' is an <http://www.haskell.org/ghc/docs/latest/html/users_guide/type-families.html#assoc-decl associated type family>
belonging to the 'Bundle' <http://en.wikipedia.org/wiki/Type_class type class>,
which, together with 'bundle' and 'unbundle' defines the isomorphism between a
product type of 'Signal's and a 'Signal' of a product type. That is, while
@(Signal a, Signal b)@ and @Signal (a,b)@ are not equal, they are /isomorphic/
and can be converted from, or to, the other using 'bundle' and 'unbundle'.

Instances of this 'Bundle' type-class are defined as /isomorphisms/ for:

  * All tuples until and including 8-tuples
  * The 'Vec'tor type

But they are defined as /identities/ for:

  * All elementary / primitive types such as: 'Bit', 'Bool', @'Signed' n@, etc.

That is:

@
instance 'Bundle' (a,b) where
  type 'Unbundled'' clk (a,b) = ('Signal'' clk a, 'Signal'' clk b)
  bundle   (a,b) = (,) '<$>' a '<*>' b
  unbundle tup   = (fst '<$>' tup, snd '<*>' tup)
@

but,

@
instance 'Bundle' Bool where
  type 'Unbundled'' clk Bool = 'Signal'' clk Bool
  bundle   s = s
  unbundle s = s
@

What you need take away from the above is that a product type (e.g. a tuple) of
'Signal's is not syntactically equal to a 'Signal' of a product type, but that
the functions of the 'Bundle' type class allow easy conversion between the two.

As a final note on this section we also want to mention the 'mealyB' function,
which does the bundling and unbundling for us:

@
mealyB :: ('Bundle' i, 'Bundle' o)
       => (s -> i -> (s,o))
       -> s
       -> ('Unbundled' i -> 'Unbundled' o)
@

Using 'mealyB' we can define @g@ as:

@
g a b c = (b1,b2,i2)
  where
    (i1,b1) = 'mealyB' f 0 (a,b)
    (i2,b2) = 'mealyB' f 3 (i1,c)
@

The general rule of thumb is: always use 'mealy', unless you do pattern matching
or construction of product types, then use 'mealyB'.
-}

{- $annotations
The 'TopEntity' annotations described in this section make it easier to put your
CλaSH design on an FPGA.

We can exert some control how the top level function is created by the CλaSH
compiler by annotating the @topEntity@ function with a 'TopEntity' annotation.
You apply these annotations using the @ANN@ pragma like so:

@
{\-\# ANN topEntity (TopEntity {t_name = ..., ...  }) \#-\}
topEntity x = ...
@

For example, given the following specification:

@
topEntity :: Signal Bit -> Signal (BitVector 8)
topEntity key1 = leds
  where
    key1R = isRising 1 key1
    leds  = mealy blinkerT (1,False,0) key1R

blinkerT (leds,mode,cntr) key1R = ((leds',mode',cntr'),leds)
  where
    -- clock frequency = 50e6   (50 MHz)
    -- led update rate = 333e-3 (every 333ms)
    cnt_max = 16650000 -- 50e6 * 333e-3

    cntr' | cntr == cnt_max = 0
          | otherwise       = cntr + 1

    mode' | key1R     = not mode
          | otherwise = mode

    leds' | cntr == 0 = if mode then complement leds
                                else rotateL leds 1
          | otherwise = leds
@

The CλaSH compiler will normally generate the following @Blinker_topEntity.vhdl@ file:

@
-- Automatically generated VHDL
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;
use IEEE.MATH_REAL.ALL;
use work.all;
use work.Blinker_types.all;

entity Blinker_topEntity is
  port(input_0         : in std_logic_vector(0 downto 0);
       -- clock
       system1000      : in std_logic;
       -- asynchronous reset: active low
       system1000_rstn : in std_logic;
       output_0        : out std_logic_vector(7 downto 0));
end;

architecture structural of Blinker_topEntity is
begin
  Blinker_topEntity_0_inst : entity Blinker_topEntity_0
    port map
      (key1_i1         => input_0
      ,system1000      => system1000
      ,system1000_rstn => system1000_rstn
      ,topLet_o        => output_0);
end;
@

However, if we add the following 'TopEntity' annotation in the file:

@
{\-\# ANN topEntity
  ('defTop'
    { t_name     = "blinker"
    , t_inputs   = [\"KEY1\"]
    , t_outputs  = [\"LED\"]
    , t_extraIn  = [ (\"CLOCK_50\", 1)
                   , (\"KEY0\"    , 1)
                   ]
    , t_clocks   = [ 'altpll' "altpll50" "CLOCK_50(0)" "not KEY0(0)" ]
    }) \#-\}
@

The CλaSH compiler will generate the following @blinker.vhdl@ file instead:

@
-- Automatically generated VHDL
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;
use IEEE.MATH_REAL.ALL;
use work.all;
use work.Blinker_types.all;

entity blinker is
  port(KEY1     : in std_logic_vector(0 downto 0);
       CLOCK_50 : in std_logic_vector(0 downto 0);
       KEY0     : in std_logic_vector(0 downto 0);
       LED      : out std_logic_vector(7 downto 0));
end;

architecture structural of blinker is
  signal system1000      : std_logic;
  signal system1000_rstn : std_logic;
  signal altpll50_locked : std_logic;
begin
  altpll50_inst : entity altpll50
    port map
      (inclk0 => CLOCK_50(0)
      ,c0     => system1000
      ,areset => not KEY0(0)
      ,locked => altpll50_locked);

  -- reset system1000_rstn is asynchronously asserted, but synchronously de-asserted
  resetSync_n_0 : block
    signal n_1 : std_logic;
    signal n_2 : std_logic;
  begin
    process(system1000,altpll50_locked)
    begin
      if altpll50_locked = '0' then
        n_1 <= '0';
        n_2 <= '0';
      elsif rising_edge(system1000) then
        n_1 <= '1';
        n_2 <= n_1;
      end if;
    end process;

    system1000_rstn <= n_2;
  end block;

  Blinker_topEntity_0_inst : entity Blinker_topEntity_0
    port map
      (key1_i1         => KEY1
      ,system1000      => system1000
      ,system1000_rstn => system1000_rstn
      ,topLet_o        => LED);
end;
@

Where we now have:

* A top-level component that is called @blinker@.
* Inputs and outputs that have a /user/-chosen name: @KEY1@, @LED@, etc.
* An instantiated <https://www.altera.com/literature/ug/ug_altpll.pdf PLL>
  component providing a stable clock signal from the free-running clock pin
  @CLOCK_50@.
* A reset that is /asynchronously/ asserted by the @lock@ signal originating from
  the PLL, meaning that your design is kept in reset until the PLL is
  providing a stable clock.
  The reset is additionally /synchronously/ de-asserted to prevent
  <http://en.wikipedia.org/wiki/Metastability_in_electronics metastability>
  of your design due to unlucky timing of the de-assertion of the reset.

See the documentation of 'TopEntity' for the meaning of all its fields.
-}

{- $primitives
There are times when you already have an existing piece of IP, or there are
times where you need the VHDL to have a specific shape so that the VHDL
synthesis tool can infer a specific component. In these specific cases you can
resort to defining your own VHDL primitives. Actually, most of the primitives
in CλaSH are specified in the same way as you will read about in this section.
There are perhaps 10 (at most) functions which are truly hard-coded into the
CλaSH compiler. You can take a look at the files in
<https://github.com/clash-lang/clash-compiler/tree/master/clash-vhdl/primitives>
(or <https://github.com/clash-lang/clash-compiler/tree/master/clash-verilog/primitives>
for the Verilog primitives or <https://github.com/clash-lang/clash-compiler/tree/master/clash-systemverilog/primitives>
for the SystemVerilog primitives) if you want to know which functions are defined
as \"regular\" primitives. The compiler looks for primitives in two locations:

* The official install location: e.g.
  * @$CABAL_DIR\/share\/\<GHC_VERSION\>\/clash-vhdl\-<VERSION\>\/primitives@
  * @$CABAL_DIR\/share\/\<GHC_VERSION\>\/clash-verilog\-<VERSION\>\/primitives@
  * @$CABAL_DIR\/share\/\<GHC_VERSION\>\/clash-systemverilog\-<VERSION\>\/primitives@
* The current directory (the location given by @pwd@)

Where redefined primitives in the current directory will overwrite those in
the official install location. For now, files containing primitive definitions
must end in the @.json@ file-extension.

CλaSH differentiates between two types of primitives, /expression/ primitives
and /declaration/ primitives, corresponding to whether the primitive is a VHDL
/expression/ or a VHDL /declaration/. We will first explore /expression/
primitives, using 'Signed' multiplication ('*') as an example. The
"CLaSH.Sized.Internal.Signed" module specifies multiplication as follows:

@
(*#) :: 'GHC.TypeLits.KnownNat' n => 'Signed' n -> 'Signed' n -> 'Signed' n
(S a) *# (S b) = fromInteger_INLINE (a * b)
{\-\# NOINLINE (*#) \#-\}
@

For which the VHDL /expression/ primitive is:

@
{ \"BlackBox\" :
  { "name"      : "CLaSH.Sized.Internal.Signed.*#"
  , "templateE" : "resize(~ARG[1] * ~ARG[2], ~LIT[0])"
  }
}
@

The @name@ of the primitive is the /fully qualified/ name of the function you
are creating the primitive for. Because we are creating an /expression/
primitive we define a @template__E__@ field. As the name suggest, it is a VHDL
/template/, meaning that the compiler must fill in the holes heralded by the
tilde (~). Here:

  * @~ARG[1]@ denotes the second argument given to the @(*#)@ function, which
    corresponds to the LHS of the ('*') operator.
  * @~ARG[2]@ denotes the third argument given to the @(*#)@ function, which
    corresponds to the RHS of the ('*') operator.
  * @~LIT[0]@ denotes the first argument given to the @(*#)@ function, with
    the extra condition that it must be a @LIT@eral. If for some reason this
    first argument does not turn out to be a literal then the compiler will
    raise an error. This first arguments corresponds to the \"@'KnownNat' n@\"
    class constraint.

An extensive list with all of the template holes will be given the end of this
section. What we immediately notice is that class constraints are counted as
normal arguments in the primitive definition. This is because these class
constraints are actually represented by ordinary record types, with fields
corresponding to the methods of the type class. In the above case, 'KnownNat'
is actually just like a @newtype@ wrapper for 'Integer'.

The second kind of primitive that we will explore is the /declaration/ primitive.
We will use 'blockRam#' as an example, for which the Haskell/CλaSH code is:

@
-- | blockRAM primitive
blockRam# :: 'KnownNat' n
          => 'SClock' clk       -- ^ 'Clock' to synchronize to
          -> 'Vec' n a          -- ^ Initial content of the BRAM, also
                              -- determines the size, @n@, of the BRAM.
                              --
                              -- __NB__: __MUST__ be a constant.
          -> 'Signal'' clk Int  -- ^ Read address @r@
          -> 'Signal'' clk Bool -- ^ Write enable
          -> 'Signal'' clk Int  -- ^ Write address @w@
          -> 'Signal'' clk a    -- ^ Value to write (at address @w@)
          -> 'Signal'' clk a
          -- ^ Value of the @blockRAM@ at address @r@ from the previous clock
          -- cycle
blockRam# clk content rd en wr din =
    'register'' clk ('errorX' "blockRam#: intial value undefined") dout
  where
    szI  = 'length' content
    dout = runST $ do
      arr <- newListArray (0,szI-1) ('toList' content)
      traverse (ramT arr) ('bundle' (rd,en,wr,din))

    ramT :: STArray s Int e -> (Int,Bool,Int,e) -> ST s e
    ramT ram (r,e,w,d) = do
      -- reading from address using an 'X' exception results in an 'X' result
      r' <- unsafeIOToST $
               catch (evaluate r >>= (return . Right))
                     (\(err :: XException) -> return (Left (throw err)))
      d' <- case r' of
              Right r2 -> readArray ram r2
              Left err -> return err
      -- writing to an address using an 'X' exception makes everything 'X'
      when e (writeArray ram w d)
      return d'
{\-\# NOINLINE blockRam# \#-\}
@

And for which the /declaration/ primitive is:

@
{ \"BlackBox\" :
    { "name" : "CLaSH.Prelude.BlockRam.blockRam#"
    , "type" :
"blockRam# :: KnownNat n       -- ARG[0]
           => SClock clk       -- clk,  ARG[1]
           -> Vec n a          -- init, ARG[2]
           -> Signal' clk Int  -- rd,   ARG[3]
           -> Signal' clk Bool -- wren, ARG[4]
           -> Signal' clk Int  -- wr,   ARG[5]
           -> Signal' clk a    -- din,  ARG[6]
           -> Signal' clk a"
    , "templateD" :
"-- blockRam begin
~GENSYM[~COMPNAME_blockRam][0] : block
  signal ~GENSYM[RAM][1] : ~TYP[2] := ~LIT[2];~IF ~VIVADO ~THEN
  signal ~GENSYM[dout][2] : std_logic_vector(~SIZE[~TYP[6]]-1 downto 0);~ELSE
  signal ~SYM[2] : ~TYP[6];~FI
  signal ~GENSYM[rd][3] : integer range 0 to ~LIT[0] - 1;
  signal ~GENSYM[wr][4] : integer range 0 to ~LIT[0] - 1;
begin
  ~SYM[3] <= to_integer(~ARG[3])
  -- pragma translate_off
                mod ~LIT[0]
  -- pragma translate_on
                ;

  ~SYM[4] <= to_integer(~ARG[5])
  -- pragma translate_off
                mod ~LIT[0]
  -- pragma translate_on
                ;

  ~GENSYM[blockRam_sync][5] : process(~CLK[1])
  begin
    if rising_edge(~CLK[1]) then
      if ~ARG[4] then~IF ~VIVADO ~THEN
        ~SYM[1](~SYM[4]) <= ~TOBV[~ARG[6]][~TYP[6]];~ELSE
        ~SYM[1](~SYM[4]) <= ~ARG[6];~FI
      end if;
      ~SYM[2] <= ~SYM[1](~SYM[3]);
    end if;
  end process;~IF ~VIVADO ~THEN
  ~RESULT <= ~FROMBV[~SYM[2]][~TYPO];~ELSE
  ~RESULT <= ~SYM[2];~FI
end block;
-- blockRam end"
    }
}
@

Again, the @name@ of the primitive is the fully qualified name of the function
you are creating the primitive for. Because we are creating a /declaration/
primitive we define a @template__D__@ field. Instead of discussing what the
individual template holes mean in the above context, we will instead just give
a general listing of the available template holes:

* @~RESULT@: VHDL signal to which the result of a primitive must be assigned
  to. NB: Only used in a /declaration/ primitive.
* @~ARG[N]@: @(N+1)@'th argument to the function.
* @~LIT[N]@: @(N+1)@'th argument to the function An extra condition that must
  hold is that this @(N+1)@'th argument is an (integer) literal.
* @~CLK[N]@: Clock signal to which the @(N+1)@'th argument is synchronized to.
* @~CLKO@: Clock signal to which the result is synchronized to.
* @~RST[N]@: Asynchronous reset signal to the clock to which the @(N+1)@'th
  argument is synchronized to.
* @~RSTO@: Asynchronous reset signal to the clock to which the result is
  synchronized to.
* @~TYP[N]@: VHDL type of the @(N+1)@'th argument.
* @~TYPO@: VHDL type of the result.
* @~TYPM[N]@: VHDL type/name/ of the @(N+1)@'th argument; used in /type/
  /qualification/.
* @~TYPM@: VHDL type/name/ of the result; used in /type qualification/.
* @~ERROR[N]@: Error value for the VHDL type of the @(N+1)@'th argument.
* @~ERRORO@: Error value for the VHDL type of the result.
* @~GENSYM[\<NAME\>][N]@: Create a unique name, trying to stay as close to
  the given @\<NAME\>@ as possible. This unique symbol can be referred to in
  other places using @~SYM[N]@.
* @~SYM[N]@: a reference to the unique symbol created by @~GENSYM[\<NAME\>][N]@.
* @~SIGD[\<HOLE\>][N]@: Create a signal declaration, using @\<HOLE\>@ as the name
  of the signal, and the type of the @(N+1)@'th argument.
* @~SIGDO[\<HOLE\>]@: Create a signal declaration, using @\<HOLE\>@ as the name
  of the signal, and the type of the result.
* @~TYPELEM[\<HOLE\>]@: The element type of the vector type represented by @\<HOLE\>@.
  The content of @\<HOLE\>@ must either be: @TYPM[N]@, @TYPO@, or @TYPELEM[\<HOLE\>]@.
* @~COMPNAME@: The name of the component in which the primitive is instantiated.
* @~LENGTH[\<HOLE\>]@: The vector length of the type represented by @\<HOLE\>@.
* @~DEPTH[\<HOLE\>]@: The tree depth of the type represented by @\<HOLE\>@.
  The content of @\<HOLE\>@ must either be: @TYPM[N]@, @TYPO@, or @TYPELEM[\<HOLE\>]@.
* @~SIZE[\<HOLE\>]@: The number of bits needed to encode the type represented by @\<HOLE\>@.
  The content of @\<HOLE\>@ must either be: @TYPM[N]@, @TYPO@, or @TYPELEM[\<HOLE\>]@.
* @~IF \<CONDITION\> ~THEN \<THEN\> ~ELSE \<ELSE\> ~FI@: renders the \<ELSE\>
  part when \<CONDITION\> evaluates to /0/, and renders the \<THEN\> in all
  other cases. Valid @\<CONDITION\>@s are @~LENGTH[\<HOLE\>]@, @~SIZE[\<HOLE\>]@,
  @~DEPTH[\<HOLE\>]@, and @~VIVADO@.
* @~VIVADO@: /1/ when CλaSH compiler is invoked with the @-clash-xilinx@ or
  @-clash-vivado@ flag. To be used with in an @~IF .. ~THEN .. ~ElSE .. ~FI@
  statement.
* @~FROMBV[\<HOLE\>][\<TYPE\>]@: create conversion code that so that the
  expression in @\<HOLE\>@ is converted to a bit vector (@std_logic_vector@).
  The @\<TYPE\>@ hole indicates the type of the expression and must be either
  @~TYP[N]@, @~TYPO@, or @~TYPELEM[\<HOLE\>]@.
* @~TOBV[\<HOLE\>][\<TYPE\>]@: create conversion code that so that the
  expression in @\<HOLE\>@, which has a bit vector (@std_logic_vector@) type, is
  converted to type indicated by @\<TYPE\>@. The @\<TYPE\>@ hole indicates the
  must be either @~TYP[N]@, @~TYPO@, or @~TYPELEM[\<HOLE\>]@.

Some final remarks to end this section: VHDL primitives are there to instruct the
CλaSH compiler to use the given VHDL template, instead of trying to do normal
synthesis. As a consequence you can use constructs inside the Haskell
definitions that are normally not synthesizable by the CλaSH compiler. However,
VHDL primitives do not give us /co-simulation/: where you would be able to
simulate VHDL and Haskell in a /single/ environment. If you still want to
simulate your design in Haskell, you will have to describe, in a cycle- and
bit-accurate way, the behaviour of that (potentially complex) IP you are trying
to include in your design.

Perhaps in the future, someone will figure out how to connect the two simulation
worlds, using e.g. VHDL's foreign function interface VHPI.
-}

{- $vprimitives
For those who are interested, the equivalent Verilog primitives are:

@
{ \"BlackBox\" :
  { "name"      : "CLaSH.Sized.Internal.Signed.*#"
  , "templateE" : "~ARG[1] * ~ARG[2]"
  }
}
@

and

@
{ \"BlackBox\" :
    { "name" : "CLaSH.Prelude.BlockRam.blockRam#"
    , "type" :
"blockRam# :: KnownNat n       -- ARG[0]
           => SClock clk       -- clk,  ARG[1]
           -> Vec n a          -- init, ARG[2]
           -> Signal' clk Int  -- rd,   ARG[3]
           -> Signal' clk Bool -- wren, ARG[4]
           -> Signal' clk Int  -- wr,   ARG[5]
           -> Signal' clk a    -- din,  ARG[6]
           -> Signal' clk a"
    , "templateD" :
"// blockRam begin
reg ~TYPO ~GENSYM[RAM][0] [0:~LIT[0]-1];
reg ~TYPO ~GENSYM[dout][1];

reg ~TYP[2] ~GENSYM[ram_init][2];
integer ~GENSYM[i][3];
initial begin
  ~SYM[2] = ~ARG[2];
  for (~SYM[3]=0; ~SYM[3] < ~LIT[0]; ~SYM[3] = ~SYM[3] + 1) begin
    ~SYM[0][~LIT[0]-1-~SYM[3]] = ~SYM[2][~SYM[3]*~SIZE[~TYPO]+:~SIZE[~TYPO]];
  end
end

always @(posedge ~CLK[1]) begin : ~GENSYM[~COMPNAME_blockRam][4]
  if (~ARG[4]) begin
    ~SYM[0][~ARG[5]] <= ~ARG[6];
  end
  ~SYM[1] <= ~SYM[0][~ARG[3]];
end

assign ~RESULT = ~SYM[1];
// blockRam end"
    }
}
@

-}

{- $svprimitives
And the equivalent SystemVerilog primitives are:

@
{ \"BlackBox\" :
  { "name"      : "CLaSH.Sized.Internal.Signed.*#"
  , "templateE" : "~ARG[1] * ~ARG[2]"
  }
}
@

and

@
{ \"BlackBox\" :
    { "name" : "CLaSH.Prelude.BlockRam.blockRam#"
    , "type" :
"blockRam# :: KnownNat n       -- ARG[0]
           => SClock clk       -- clk,  ARG[1]
           -> Vec n a          -- init, ARG[2]
           -> Signal' clk Int  -- rd,   ARG[3]
           -> Signal' clk Bool -- wren, ARG[4]
           -> Signal' clk Int  -- wr,   ARG[5]
           -> Signal' clk a    -- din,  ARG[6]
           -> Signal' clk a"
    , "templateD" :
"// blockRam begin
~SIGD[~GENSYM[RAM][0]][2];
logic [~SIZE[~TYP[6]]-1:0] ~GENSYM[dout][1];
initial begin
  ~SYM[0] = ~LIT[2];
end
always @(posedge ~CLK[1]) begin : ~GENSYM[~COMPNAME_blockRam][2]
  if (~ARG[4]) begin
    ~SYM[0][~ARG[5]] <= ~TOBV[~ARG[6]][~TYP[6]];
  end
  ~SYM[1] <= ~SYM[0][~ARG[3]];
end
assign ~RESULT = ~FROMBV[~SYM[1]][~TYP[6]];
// blockRam end"
    }
  }
@

-}

{- $multiclock #multiclock#
CλaSH supports multi-clock designs, though perhaps in a slightly limited form.
What is possible is:

* Explicitly assign clocks to memory primitives.
* Synchronise between differently-clocked parts of your design in a type-safe
  way.

What is /not/ possible is:

* Generate a clock signal in module A, and assign this clock signal to a memory
  primitive in module B.

What this means is that when CλaSH converts your design to VHDL/(System)Verilog,
you end up with a top-level module/entity with multiple clock and reset ports
for the different clock domains. If you're targeting an FPGA, you can use e.g. a
<https://www.altera.com/literature/ug/ug_altpll.pdf PPL> or
<http://www.xilinx.com/support/documentation/user_guides/ug472_7Series_Clocking.pdf MMCM>
to provide the clock signals.

== Building a FIFO synchroniser

This part of the tutorial assumes you know what <https://en.wikipedia.org/wiki/Metastability_in_electronics metastability>
is, and how it can never truly be avoided in any asynchronous circuit. Also
it assumes that you are familiar with the design of synchronizer circuits, and
why a dual flip-flop synchroniser only works for bit-synchronisation and not
word-synchronisation.
The explicitly clocked versions of all synchronous functions and primitives can
be found in "CLaSH.Prelude.Explicit", which also re-exports the functions in
"CLaSH.Signal.Explicit". We will use those functions to create a FIFO where
the read and write port are synchronised to different clocks. Below you can find
the code to build the FIFO synchroniser based on the design described in:
<http://www.sunburst-design.com/papers/CummingsSNUG2002SJ_FIFO1.pdf>

We start with enable a few options that will make writing the type-signatures for
our components a bit easier. We'll also import the standard "CLaSH.Prelude"
module, and the "CLaSH.Prelude.Explicit" module for our explicitly clocked
synchronous functions:

@
{\-\# LANGUAGE PartialTypeSignatures \#-\}
{\-\# OPTIONS_GHC -fno-warn-partial-type-signatures \#-\}
module MultiClockFifo where

import CLaSH.Prelude
import CLaSH.Prelude.Explicit
import Data.Maybe             (isJust)
@

Then we'll start with the /heart/ of the FIFO synchroniser, an asynchronous RAM
in the form of 'asyncRam''. It's called an asynchronous RAM because the read
port is not synchronised to any clock (though the write port is). Note that in
CλaSH we don't really have asynchronous logic, there is only combinational and
synchronous logic. As a consequence, we see in the type signature of 'asyncRam'':

@
__asyncRam'__
  :: _
  => SClock wclk                   -- ^ Clock to which to synchronise the write port of the RAM
  -> SClock rclk                   -- ^ Clock to which the read address signal __r__ is synchronised
  -> SNat n                        -- ^ Size __n__ of the RAM
  -> Signal' rclk addr             -- ^ Read address __r__
  -> Signal' wclk (Maybe (addr,a)) -- ^ (write address @w@, value to write)
  -> Signal' rclk a                -- ^ Value of the RAM at address __r__
@

that the signal containing the read address __r__ is synchronised to a different
clock. That is, there is __no__ such thing as an @AsyncSignal@ in CλaSH.

We continue by instantiating the 'asyncRam'':

@
fifoMem wclk rclk addrSize wfull raddr wdataM =
  'asyncRam'' wclk rclk
            ('pow2SNat' addrSize)
            raddr
            ('mux' (not \<$\> wfull)
                 wdataM
                 (pure Nothing))
@

We see that we give it @2^addrSize@ elements, where @addrSize@ is the bit-size
of the address. Also, we only write new values to the RAM when a new write is
requested, indicated by @wdataM@ having a $Just$ value, and the buffer is not
full, indicated by @wfull@.

The next part of the design calculates the read and write address for the
asynchronous RAM, and creates the flags indicating whether the FIFO is full
or empty. The address and flag generator is given in 'mealy' machine style:

@
ptrCompareT addrSize flagGen (bin,ptr,flag) (s_ptr,inc) =
    ((bin',ptr',flag')
    ,(flag,addr,ptr))
  where
    -- GRAYSTYLE2 pointer
    bin' = bin + 'boolToBV' (inc && not flag)
    ptr' = (bin' \`shiftR\` 1) \`xor\` bin'
    addr = 'slice' (addrSize ``subSNat`` d1) d0 bin

    flag' = flagGen ptr' s_ptr
@

It is parametrised in both address size, @addrSize@, and status flag generator,
@flagGen@. It has two inputs, @s_ptr@, the synchronised pointer from the other
clock domain, and @inc@, which indicates we want to perform a write or read of
the FIFO. It creates three outputs: @flag@, the full or empty flag, @addr@, the
read or write address into the RAM, and @ptr@, the Gray-encoded version of the
read or write address which will be synchronised between the two clock domains.

Next follow the initial states of address generators, and the flag generators
for the empty and full flags:

@
-- FIFO empty: when next pntr == synchronized wptr or on reset
isEmpty       = (==)
rptrEmptyInit = (0,0,True)

-- FIFO full: when next pntr == synchronized {~wptr[addrSize:addrSize-1],wptr[addrSize-2:0]}
isFull addrSize ptr s_ptr =
    ptr == 'complement' ('slice' addrSize (addrSize ``subSNat`` d1) s_ptr) '++#'
                      'slice' (addrSize ``subSNat`` d2) d0  s_ptr

wptrFullInit        = (0,0,False)
@

We create a dual flip-flop synchroniser to be used to synchronise the
Gray-encoded pointers between the two clock domains:

@
ptrSync clk1 clk2 = 'register'' clk2 0
                  . 'register'' clk2 0
                  . 'unsafeSynchronizer' clk1 clk2
@

It uses the 'unsafeSynchroniser' primitive, which is needed to go from one clock
domain to the other. All synchronizers are specified in terms of
'unsafeSynchronizer' (see for example the <src/CLaSH-Prelude-RAM.html#line-103 source of asyncRam#>).
The 'unsafeSynchronizer' primitive is turned into a (bundle of) wire(s) by the
CλaSH compiler, so developers must ensure that it is only used as part of a
proper synchronizer.

Finally we combine all the component in:

@
fifo
  :: _
  => SNat (addrSize + 2)
  -> SClock wclk
  -> SClock rclk
  -> Signal' rclk Bool
  -> Signal' wclk (Maybe a)
  -> (Signal' rclk a, Signal' rclk Bool, Signal' wclk Bool)
fifo addrSize wclk rclk rinc wdataM = (rdata,rempty,wfull)
  where
    s_rptr = ptrSync rclk wclk rptr
    s_wptr = ptrSync wclk rclk wptr

    rdata = fifoMem wclk rclk addrSize wfull raddr
               (liftA2 (,) \<$\> (Just \<$\> waddr) \<*\> wdataM)

    (rempty,raddr,rptr) = 'mealyB'' rclk (ptrCompareT addrSize isEmpty) rptrEmptyInit
                                  (s_wptr,rinc)

    (wfull,waddr,wptr)  = 'mealyB'' wclk (ptrCompareT addrSize (isFull addrSize))
                                  wptrFullInit (s_rptr,isJust \<$\> wdataM)
@

where we first specify the synchronisation of the read and the write pointers,
instantiate the asynchronous RAM, and instantiate the read address \/ pointer \/
flag generator and write address \/ pointer \/ flag generator.

Ultimately, the whole file containing our FIFO design will look like this:

@
{\-\# LANGUAGE PartialTypeSignatures \#-\}
{\-\# OPTIONS_GHC -fno-warn-partial-type-signatures \#-\}
module MultiClockFifo where

import CLaSH.Prelude
import CLaSH.Prelude.Explicit
import Data.Maybe             (isJust)

fifoMem wclk rclk addrSize wfull raddr wdataM =
  'asyncRam'' wclk rclk
            ('pow2SNat' addrSize)
            raddr
            ('mux' (not \<$\> wfull)
                 wdataM
                 (pure Nothing))

ptrCompareT addrSize flagGen (bin,ptr,flag) (s_ptr,inc) =
    ((bin',ptr',flag')
    ,(flag,addr,ptr))
  where
    -- GRAYSTYLE2 pointer
    bin' = bin + 'boolToBV' (inc && not flag)
    ptr' = (bin' \`shiftR\` 1) \`xor\` bin'
    addr = 'slice' (addrSize ``subSNat`` d1) d0 bin

    flag' = flagGen ptr' s_ptr

-- FIFO empty: when next pntr == synchronized wptr or on reset
isEmpty       = (==)
rptrEmptyInit = (0,0,True)

-- FIFO full: when next pntr == synchronized {~wptr[addrSize:addrSize-1],wptr[addrSize-2:0]}
isFull addrSize ptr s_ptr =
    ptr == 'complement' ('slice' addrSize (addrSize ``subSNat`` d1) s_ptr) '++#'
                      'slice' (addrSize ``subSNat`` d2) d0  s_ptr

wptrFullInit        = (0,0,False)

-- Dual flip-flop synchroniser
ptrSync clk1 clk2 = 'register'' clk2 0
                  . 'register'' clk2 0
                  . 'unsafeSynchronizer' clk1 clk2

-- Async FIFO synchroniser
fifo
  :: _
  => SNat (addrSize + 2)
  -> SClock wclk
  -> SClock rclk
  -> Signal' rclk Bool
  -> Signal' wclk (Maybe a)
  -> (Signal' rclk a, Signal' rclk Bool, Signal' wclk Bool)
fifo addrSize wclk rclk rinc wdataM = (rdata,rempty,wfull)
  where
    s_rptr = ptrSync rclk wclk rptr
    s_wptr = ptrSync wclk rclk wptr

    rdata = fifoMem wclk rclk addrSize wfull raddr
               (liftA2 (,) \<$\> (Just \<$\> waddr) \<*\> wdataM)

    (rempty,raddr,rptr) = 'mealyB'' rclk (ptrCompareT addrSize isEmpty) rptrEmptyInit
                                  (s_wptr,rinc)

    (wfull,waddr,wptr)  = 'mealyB'' wclk (ptrCompareT addrSize (isFull addrSize))
                                  wptrFullInit (s_rptr,isJust \<$\> wdataM)
@

== Instantiating a FIFO synchroniser

Having finished our FIFO synchroniser it's time to instantiate with concrete
clock domains. Let us assume we have part of our system connected to an ADC
which runs at 20 MHz, and we have created an FFT component running at only 9 MHz,
while the rest of our system runs at 50 MHz. What we want to do connect part
of our design connected to the ADC, and running at 20 MHz, to part of our design
connected to the FFT running at 9 MHz.

First, we must calculate the relative clock periods using 'freqCalc':

>>> freqCalc [20,9,50]
[45,100,18]

We can then create the clocks:

@
type ClkADC = 'Clk \"ADC\"    45
type ClkFFT = 'Clk \"FFT\"    100
type ClkSys = 'Clk \"System\" 18

clkADC :: SClock ClkADC
clkADC = sclock

clkFFT :: SClock ClkFFT
clkFFT = sclock

clkSys :: SClock ClkSys
clkSys = sclock
@

and subsequently a 256-space FIFO synchroniser that safely bridges the ADC clock
domain and to the FFT clock domain:

@
adcToFFT
  :: Signal' ClkFFT Bool
  -> Signal' ClkADC (Maybe (SFixed 8 8))
  -> (Signal' ClkFFT (SFixed 8 8), Signal' ClkFFT Bool, Signal' ClkADC Bool)
adcToFFT = fifo d8 clkADC clkFFT
@

-}

{- $conclusion
For now, this is the end of this tutorial. We will be adding updates over time,
so check back from time to time. For now, we recommend that you continue with
exploring the "CLaSH.Prelude" module, and get a better understanding of the
capabilities of CλaSH in the process.
-}

{- $errorsandsolutions
A list of often encountered errors and their solutions:

* __Type error: Couldn't match expected type @'Signal' (a,b)@ with actual type__
  __@('Signal' a, 'Signal' b)@__:

    Signals of product types and product types (to which tuples belong) of
    signals are __isomorphic__ due to synchronisity principle, but are not
    (structurally) equal. Use the 'bundle' function to convert from a product type
    to the signal type. So if your code which gives the error looks like:

    @
    ... = f a b (c,d)
    @

    add the 'bundle'' function like so:

    @
    ... = f a b ('bundle' (c,d))
    @

    Product types supported by 'bundle' are:

    * All tuples until and including 8-tuples
    * The 'Vec'tor type

    NB: Use 'bundle'' when you are using explicitly clocked @'Signal''@s

* __Type error: Couldn't match expected type @('Signal' a, 'Signal' b)@ with__
  __ actual type @'Signal' (a,b)@__:

    Product types (to which tuples belong) of signals and signals of product
    types are __isomorphic__ due to synchronicity principle, but are not
    (structurally) equal. Use the 'unbundle' function to convert from a signal
    type to the product type. So if your code which gives the error looks like:

    @
    (c,d) = f a b
    @

    add the 'unbundle' function like so:

    @
    (c,d) = 'unbundle' (f a b)
    @

    Product types supported by 'unbundle' are:

    * All tuples until and including 8-tuples
    * The 'Vec'tor type

    NB: Use 'unbundle'' when you are using explicitly clocked @'Signal''@s

* __CLaSH.Netlist(..): Not in normal form: \<REASON\>: \<EXPR\>__:

    A function could not be transformed into the expected normal form. This
    usually means one of the following:

    * The @topEntity@ has residual polymorphism.
    * The @topEntity@ has higher-order arguments, or a higher-order result.
    * You are using types which cannot be represented in hardware.

    The solution for all the above listed reasons is quite simple: remove them.
    That is, make sure that the @topEntity@ is completely monomorphic and
    first-order. Also remove any variables and constants/literals that have a
    non-representable type, see <#unsupported Unsupported Haskell features> to
    find out which types are not representable.

* __CLaSH.Normalize(94): Expr belonging to bndr: \<FUNCTION\> remains__
  __recursive after normalization__:

    * If you actually wrote a recursive function, rewrite it to a non-recursive
      one using e.g. one of the higher-order functions in "CLaSH.Sized.Vector" :-)

    * You defined a recursively defined value, but left it polymorphic:

    @
    topEntity x y = acc
      where
        acc = 'register' 3 (acc + x * y)
    @

    The above function, works for any number-like type. This means that @acc@ is
    a recursively defined __polymorphic__ value. Adding a monomorphic type
    annotation makes the error go away:

    @
    topEntity :: 'Signal' ('Signed' 8) -> 'Signal' ('Signed' 8) -> 'Signal' ('Signed' 8)
    topEntity x y = acc
      where
        acc = 'register' 3 (acc + x * y)
    @

    Or, alternatively:

    @
    topEntity x y = acc
      where
        acc = 'register' (3 :: 'Signed' 8) (acc + x * y)
    @

* __CLaSH.Normalize.Transformations(155): InlineNonRep: \<FUNCTION\> already__
  __inlined 100 times in:\<FUNCTION\>, \<TYPE\>__:

    You left the @topEntity@ function polymorphic or higher-order: use
    @:t topEntity@ to check if the type is indeed polymorphic or higher-order.
    If it is, add a monomorphic type signature, and / or supply higher-order
    arguments.

* __Can't make testbench for: \<LONG_VERBATIM_COMPONENT_DESCRIPTION\>__:

    * Don't worry, it's actually only a warning.

    * The @topEntity@ function does __not__ have exactly 1 argument. If your
      @topEntity@ has no arguments, you're out of luck for now. If it has
      multiple arguments, consider bundling them in a tuple.

*  __\<*** Exception: \<\<loop\>\>__ or "blinking cursor"

    You are using value-recursion, but one of the 'Vec'tor functions that you
    are using is too /strict/ in one of the recursive arguments. For example:

    @
    -- Bubble sort for 1 iteration
    sortV xs = 'map' fst sorted ':<' (snd ('last' sorted))
     where
       lefts  = 'head' xs :> 'map' snd ('init' sorted)
       rights = 'tail' xs
       sorted = 'zipWith' compareSwapL lefts rights

    -- Compare and swap
    compareSwapL a b = if a < b then (a,b)
                                else (b,a)
    @

    Will not terminate because 'zipWith' is too strict in its second argument.

    In this case, adding 'lazyV' on 'zipWith's second argument:

    @
    sortVL xs = 'map' fst sorted ':<' (snd ('last' sorted))
     where
       lefts  = 'head' xs :> map snd ('init' sorted)
       rights = 'tail' xs
       sorted = 'zipWith' compareSwapL ('lazyV' lefts) rights
    @

    Results in a successful computation:

    >>> sortVL (4 :> 1 :> 2 :> 3 :> Nil)
    <1,2,3,4>
-}

{- $limitations #limitations#
Here is a list of Haskell features for which the CλaSH compiler has only
/limited/ support (for now):

* __Recursively defined functions__

    At first hand, it seems rather bad that a compiler for a functional language
    cannot synthesize recursively defined functions to circuits. However, when
    viewing your functions as a /structural/ specification of a circuit, this
    /feature/ of the CλaSH compiler makes sense. Also, only certain types of
    recursion are considered non-synthesisable; recursively defined values are
    for example synthesisable: they are (often) synthesized to feedback loops.

    Let us distinguish between three variants of recursion:

    * __Dynamic data-dependent recursion__

        As demonstrated in this definition of a function that calculates the
        n'th Fibbonacci number:

        @
        fibR 0 = 0
        fibR 1 = 1
        fibR n = fibR (n-1) + fibR (n-2)
        @

        To get the first 10 numbers, we do the following:

        >>> import qualified Data.List as L
        >>> L.map fibR [0..9]
        [0,1,1,2,3,5,8,13,21,34]

        The @fibR@ function is not synthesizable by the CλaSH compiler, because,
        when we take a /structural/ view, @fibR@ describes an infinitely deep
        structure.

        In principal, descriptions like the above could be synthesized to a
        circuit, but it would have to be a /sequential/ circuit. Where the most
        general synthesis would then require a stack. Such a synthesis approach
        is also known as /behavioural/ synthesis, something which the CλaSH
        compiler simply does not do. One reason that CλaSH does not do this is
        because it does not fit the paradigm that only functions working on
        values of type 'Signal' result in sequential circuits, and all other
        (non higher-order) functions result in combinational circuits. This
        paradigm gives the designer the most straightforward mapping from the
        original Haskell description to generated circuit, and thus the greatest
        control over the eventual size of the circuit and longest propagation
        delay.

    * __Value-recursion__

        As demonstrated in this definition of a function that calculates the
        n'th Fibbonaci number on the n'th clock cycle:

        @
        fibS = r
          where r = 'register' 0 r + 'register' 0 ('register' 1 r)
        @

        To get the first 10 numbers, we do the following:

        >>> sampleN 10 fibS
        [0,1,1,2,3,5,8,13,21,34]

        Unlike the @fibR@ function, the above @fibS@ function /is/ synthesisable
        by the CλaSH compiler. Where the recursively defined (non-function)
        value /r/ is synthesized to a feedback loop containing three registers
        and one adder.

        Note that not all recursively defined values result in a feedback loop.
        An example that uses recursively defined values which does not result
        in a feedback loop is the following function that performs one iteration
        of bubble sort:

        @
        sortV xs = 'map' fst sorted :< (snd ('last' sorted))
         where
           lefts  = 'head' xs :> 'map' snd ('init' sorted)
           rights = 'tail' xs
           sorted = 'zipWith' compareSwapL lefts rights
        @

        Where we can clearly see that 'lefts' and 'sorted' are defined in terms
        of each other. Also the above @sortV@ function /is/ synthesisable.

    * __Static/Structure-dependent recursion__

        Static, or, structure-dependent recursion is a rather /vague/ concept.
        What we mean by this concept are recursive definitions where a user can
        sensibly imagine that the recursive definition can be completely
        unfolded (all recursion is eliminated) at compile-time in a finite
        amount of time.

        Such definitions would e.g. be:

        @
        mapV :: (a -> b) -> Vec n a -> Vec n b
        mapV _ Nil         = Nil
        mapV f (Cons x xs) = Cons (f x) (mapV f xs)

        topEntity :: Vec 4 Int -> Vec 4 Int
        topEntity = mapV (+1)
        @

        Where one can imagine that a compiler can unroll the definition of
        @mapV@ four times, knowing that the @topEntity@ function applies @mapV@
        to a 'Vec' of length 4. Sadly, the compile-time evaluation mechanisms in
        the CλaSH compiler are very poor, and a user-defined function such as
        the @mapV@ function defined above, is /currently/ not synthesisable.
        We /do/ plan to add support for this in the future. In the mean time,
        this poor support for user-defined recursive functions is amortized by
        the fact that the CλaSH compiler has built-in support for the
        higher-order functions defined in "CLaSH.Sized.Vector". Most regular
        design patterns often encountered in circuit design are captured by the
        higher-order functions in "CLaSH.Sized.Vector".

* __Recursive datatypes__

    The CλaSH compiler needs to be able to determine a bit-size for any value
    that will be represented in the eventual circuit. More specifically, we need
    to know the maximum number of bits needed to represent a value. While this
    is trivial for values of the elementary types, sum types, and product types,
    putting a fixed upper bound on recursive types is not (always) feasible.
    This means that the ubiquitous list type is unsupported! The only recursive
    type that is currently supported by the CλaSH compiler is the 'Vec'tor type,
    for which the compiler has hard-coded knowledge.

    For \"easy\" 'Vec'tor literals you should use Template Haskell splices and
    the 'listToVecTH' /meta/-function that as we have seen earlier in this tutorial.

* __GADT pattern matching__

    While pattern matching for regular ADTs is supported, pattern matching for
    GADTs is __not__. The constructors 'Cons' and 'Nil' of the 'Vec'tor type,
    which is also a GADT, are __no__ exception! However, you can use the
    convenient ':>' pattern synonym.

* __Floating point types__

    There is no support for the 'Float' and 'Double' types, if you need numbers
    with a /fractional/ part you can use the 'Fixed' point type.

    As to why there is no support for these floating point types:

        1.  In order to achieve reasonable operating frequencies, arithmetic
            circuits for floating point data types must be pipelined.
        2.  Haskell's primitive arithmetic operators on floating point data types,
            such as 'plusFloat#'

            @
            __plusFloat#__ :: 'Float#' -> 'Float#' -> 'Float#'
            @

            which underlie @'Float'@'s 'Num' instance, must be implemented as
            purely combinational circuits according to their type. Remember,
            sequential circuits operate on values of type \"@'Signal' a@\".

    Although it is possible to implement purely combinational (not pipelined)
    arithmetic circuits for floating point data types, the circuit would be
    unreasonable slow. And so, without synthesis possibilities for the basic
    arithmetic operations, there is no point in supporting the floating point
    data types.

* __Haskell primitive types__

    Only the following primitive Haskell types are supported:

        * 'Integer'
        * 'Int'
        * 'Int8'
        * 'Int16'
        * 'Int32'
        * 'Int64' (not available when compiling with @-clash-intwidth=32@ on a 64-bit machine)
        * 'Word'
        * 'Word8'
        * 'Word16'
        * 'Word32'
        * 'Word64' (not available when compiling with @-clash-intwidth=32@ on a 64-bit machine)
        * 'Char'

    There are several aspects of which you should take note:

        *   'Int' and 'Word' are represented by the same number of bits as is
            native for the architecture of the computer on which the CλaSH
            compiler is executed. This means that if you are working on a 64-bit
            machine, 'Int' and 'Word' will be 64-bit. This might be problematic
            when you are working in a team, and one designer has a 32-bit
            machine, and the other has a 64-bit machine. In general, you should
            be avoiding 'Int' in such cases, but as a band-aid solution, you can
            force the CλaSH compiler to use a specific bit-width for `Int` and
            `Word` using the @-clash-intwidth=N@ flag, where /N/ must either be
            /32/ or /64/.

        *   When you use the @-clash-intwidth=32@ flag on a /64-bit/ machine,
            the 'Word64' and 'Int64' types /cannot/ be translated. This
            restriction does /not/ apply to the other three combinations of
            @-clash-intwidth@ flag and machine type.

        *   The translation of 'Integer' is not meaning-preserving. 'Integer' in
            Haskell is an arbitrary precision integer, something that cannot
            be represented in a statically known number of bits. In the CλaSH
            compiler, we chose to represent 'Integer' by the same number of bits
            as we do for 'Int' and 'Word'. As you have read in a previous
            bullet point, this number of bits is either 32 or 64, depending on
            the architecture of the machine the CλaSH compiler is running on, or
            the setting of the @-clash-intwidth@ flag.

            Consequently, you should use `Integer` with due diligence; be
            especially careful when using `fromIntegral` as it does a conversion
            via 'Integer'. For example:

                > signedToUnsigned :: Signed 128 -> Unsigned 128
                > signedToUnsigned = fromIntegral

            can either lose the top 64 or 96 bits depending on whether 'Integer'
            is represented by 64 or 32 bits. Instead, when doing such conversions,
            you should use 'bitCoerce':

                > signedToUnsigned :: Signed 128 -> Unsigned 128
                > signedToUnsigned = bitCoerce

* __Side-effects: 'IO', 'ST', etc.__

    There is no support for side-effecting computations such as those in the
    'IO' or 'ST' monad. There is also no support for Haskell's
    <http://www.haskell.org/haskellwiki/Foreign_Function_Interface FFI>.
-}

{- $vslava
In Haskell land the most well-known way of describing digital circuits is the
Lava family of languages:

* <http://hackage.haskell.org/package/chalmers-lava2000 Chalmers Lava>
* <http://hackage.haskell.org/package/xilinx-lava Xilinx Lava>
* <http://hackage.haskell.org/package/york-lava York Lava>
* <http://hackage.haskell.org/package/kansas-lava Kansas Lava>

The big difference between CλaSH and Lava is that CλaSH uses a \"standard\"
compiler (static analysis) approach towards synthesis, where Lava is an
embedded domain specific language. One downside of static analysis vs. the
embedded language approach is already clearly visible: synthesis of recursive
descriptions does not come for \"free\". This will be implemented in CλaSH in
due time, but that doesn't help the circuit designer right now. As already
mentioned earlier, the poor support for recursive functions is amortized by
the built-in support for the higher-order in "CLaSH.Sized.Vector".

The big upside of CλaSH and its static analysis approach is that CλaSH can
do synthesis of \"normal\" functions: there is no forced encasing datatype (often
called /Signal/ in Lava) on all the arguments and results of a synthesizable
function. This enables the following features not available to Lava:

* Automatic synthesis for user-defined ADTs
* Synthesis of all choice constructs (pattern matching, guards, etc.)
* 'Applicative' instance for the 'Signal' type
* Working with \"normal\" functions permits the use of e.g. the
  'Control.Monad.State.Lazy.State' monad to describe the functionality of a
  circuit.

Although there are Lava alternatives to some of the above features (e.g.
first-class patterns to replace pattern matching) they are not as \"beautiful\"
and / or easy to use as the standard Haskell features.
-}
