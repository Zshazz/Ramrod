Ramrod
======

Ramrod, the Nimrod Random Library

#Key Features
For RNGs the interface currently is:

    proc newRng*(RNG: typedesc[...]): RNG
    proc newRng*[IntType: TInteger
            ](RNG: typedesc[...], seed: IntType): RNG
    proc newRng*(RNG: typedesc[...],
              seed: iterator(): TInteger {.closure.}): RNG
    proc next*[RNG: ...
          ](self: RNG, T: typedesc[TInteger]): T
    proc reset*[RNG: ..., IntType: TInteger
            ](self: var RNG, seed: IntType)
    proc reset*[RNG: ...
                ](self: var RNG, seed: iterator(): TInteger {.closure.})
    proc remix*[RNG: ..., IntType: TInteger
            ](self: var RNG, seed: IntType)
    proc remix*[RNG: ...
                ](self: var RNG, seed: iterator(): TInteger {.closure.})

Biggest awesome thing about this: pass it an iterator giving out integers of any size and it'll magically convert them for you! So it can basically work from any source without much of a bother.

#Possible future directions
- xorshift (128 & 1024 varieties) ... appears pretty easy to implement and it's fairly powerful
- ramrod.common (something like rolling an int in a particular range and Knuth shuffle are some good baseline procedures)