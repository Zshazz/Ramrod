#
# Ramrod, the Nimrod Random library
# (c) Copyright 2014 Chris Cain (zshazz)
#
# Licensed under MIT (see LICENSE)
#
# file: isaac.nim

## This module implements the ISAAC fast "cryptographic" Random Number Generator.
##
## For reference: http://burtleburtle.net/bob/rand/isaacafa.html
##
## If you do not know what you're doing, do NOT use this implementation with the
## expectation of it being secure! As of this writing, this code has NOT been
## vetted by any real cryptographers and, thus, should be assumed to be a weak
## interpretation of the original algorithm. I can guarantee that, despite being
## aware of possibility of them, I have not put any effort to defeat side-channel
## attacks.
##
## Hopefully this notice has sufficiently scared you away from using this for your
## online real-money poker game unless you pay a proper cryptographer to carefully
## inspect the code below. If you do such a thing, please let me know of any
## corrections that can be made ASAP.
##
## That said, the intended purpose of this ISAAC PRNG implementation is to provide
## a native Nimrod way to get very, very high-quality pseudorandom numbers for
## applications (especially games, since ISAAC is still reasonably fast). In
## general, this should be preferred to linear congruential RNGs. In an analysis
## on the original ISAAC implementation (NOT THIS NIMROD IMPLEMENTATION), it was
## found that ISAAC is a secure cryptographic-grade RNG, which makes it superior
## (for some purposes) to even "really good" well known RNGs like Mersenne
## Twister 19937. Some suggest that not enough cryptanalysis has been done on the
## original algorithm, so it's possible that even the original might be later
## found to have weaknesses.
##
## Also included is an implementation of the "ISAAC+" variation of ISAAC.
## Refer to the paper below:
## 
## http://eprint.iacr.org/2006/438.pdf
##
## It appears to me that the paper described ISAAC incorrectly (Algorithm 1.1
## fails to `xor a` at line 6) thus the described weakness may or may not exist.
## Furthermore, the proposed "ISAAC+" variation fails to perform this step as
## well. Because of that, my implementation of ISAAC+ has the `xor a` that
## "ISAAC+" does not do, to make it better match the original algorithm (since
## the omission appears to be a mistake ... please correct me if I'm wrong).
## Due to the change, I cannot, in good conscience, call it "ISAAC+" and mislead
## anyone into thinking it has been properly analyzed to be better. At best,
## consider it to simply be a variation of ISAAC. At worst, it could be
## vulnerable to attacks that the original does not have. Use at your own risk.
##
## To get a good grasp of what kind of RNG you should use, you should analyze
## each in the context of your application to make an informed decision. For
## general (i.e. "safe" for a very liberal definition of safe considering the
## fact that this code has NOT been vetted) use cases, ISAAC is my personal
## preference. MT19937 is often used for general use cases as well, and it's
## also not a bad choice. However, a linear congruential RNG is a relatively
## poor choice. Despite being easier to generate small sequences of random
## numbers, it is still not significantly faster than even the "cryptographically
## secure" ISAAC implementation in the context of a real application but makes
## it very easy for anyone aware to guess the next number in the sequence.
## Use a LCG only in cases that you want "smart individuals" to be able to
## figure out the sequence.

import unsigned, util

const
  isaacSizeL = 8              ## logarithmic size of internal state
  isaacSize* = 1 shl isaacSizeL  ## size of internal state
  isaacMask = (isaacSize-1) ## Mask to look into parts of the state during
                            ## the RNG steps
  goldenNum = 0x9e3779b9'i32  ## "Magic Number" used in many hash functions

type
  TIsaacRng = object
    cursor: int32   ## The position in the internal state the next draw will
                    ## come from
    acc,last,count: int32   ## A few variables used in generation that need \
      ## to be retained.
      ##
      ## Note that the types of these are different than the C implementation
      ## in two important ways:
      ##
      ## 1. This is signed, not unsigned. However, from my analysis, this is
      ## unimportant as unsigned arithmetic can be used where necessary and it
      ## will ultimately be byte-for-byte identical to an implementation that
      ## uses unsigned
      ##
      ## 2. The original C implementation uses an `unsigned long int` which,
      ## when written, meant a unsigned 4-byte quantity. Modern compilers can
      ## (and often do) treat this as an 8-byte number. However, the original
      ## author's intent is preserved by using a Nimrod `int32`.
      ##
      ## An unimportant change is that the names of the variables have been
      ## changed from `a,b,c`. Considering the original code has other unrelated
      ## variables also named `a,b,c`, this will represent a massive readability
      ## enhancement.
    rsl, mem: array[isaacSize, int32] ## Holds internal state as well as
                                      ## isaacSizeL generated numbers.
                                      ## Ditto on the type notes
  TIsaacMinusRng {.borrow: `.`.} = distinct TIsaacRng
  PIsaacRng*  = ref TIsaacRng
    ## Instance of an ISAAC PRNG
  PIsaacMinusRng* = ref TIsaacMinusRng
    ## Instance of an "ISAAC+" PRNG

{.push overflowChecks: off.} # Overflow can happen, and intended by algorithm

proc refill[RNG: PIsaacRng|PIsaacMinusRng](self: RNG) =
  ## In the original c implementation, this was called the `isaac` function
  ##
  ## This procedure refreshs the internal buffer `rsl` of the IsaacRng, intended
  ## for initializing or when the entire random number buffer has been used up
  inc self.count  # increment once per 256 results
  var
    acc = self.acc
    last = self.last + self.count # then combine with the last result's
                                  # random number
    mem = addr(self.mem)  # Have a direct link to mem to minimize indirections
    rsl = addr(self.rsl)  # ditto for rsl
    x {.noInit.}: type(mem[0])  # saves the state of mem[i] for each step

    i: int = 0
    j: int = isaacSize div 2  # Always (i + isaacSize/2) mod isaacSize
  
  template opr(T: typedesc[PIsaacRng], v, amt: int32): int32 =
    (v shr amt)
  template opl(T: typedesc[PIsaacRng], v, amt: int32): int32 =
    (v shl amt)
  template opr(T: typedesc[PIsaacMinusRng], v, amt: int32): int32 =
    ((v shr amt) or (v shl (32 - amt)))
  template opl(T: typedesc[PIsaacMinusRng], v, amt: int32): int32 =
    ((v shl amt) or (v shr (32 - amt)))
  template fit(e: expr): expr = (e) and isaacMask
  template middleStep(T: typedesc[PIsaacRng]): stmt =
    mem[i] = acc + last + mem[fit(   x   shr  2)]
    rsl[i] =     x      + mem[fit(mem[i] shr 10)]
  template middleStep(T: typedesc[PIsaacMinusRng]): stmt =
    mem[i] = (acc xor last) +  mem[fit(T.opr(     x,  2))]
    rsl[i] =    (x + acc)  xor mem[fit(T.opr(mem[i], 10))]
  template rngStep(mix: expr): stmt =
    x = mem[i]
    acc = (acc xor (mix)) + mem[j]
    RNG.middleStep()
    last = rsl[i]
    inc i; inc j

  while j < isaacSize:
    rngStep(RNG.opl(acc, 13)); rngStep(RNG.opr(acc,  6))
    rngStep(RNG.opl(acc,  2)); rngStep(RNG.opr(acc, 16))

  j = 0   # wrap j around before continuing
  while i < isaacSize:
    rngStep(RNG.opl(acc, 13)); rngStep(RNG.opr(acc,  6))
    rngStep(RNG.opl(acc,  2)); rngStep(RNG.opr(acc, 16))

  self.last = last
  self.acc = acc

proc init[T: PIsaacRng|PIsaacMinusRng](self: T, useSeed: bool) =
  ## Initialize the generator. When useSeed is true, this should use the seed
  ## stored in self.rsl in the initialization. Otherwise, it is NOT used.
  var a,b,c,d,e,f,g,h = goldenNum
  self.acc = 0
  self.last = 0
  self.count = 0
  for i in 0..high(self.mem):
    self.mem[i] = 0
  # self.rsl should not be initted because that's where the seed comes from

  # Wanted: template mix(a,b,c,d,e,f,g,h: int32{sym})
  # Error: undeclared identifier: 'sym'
  # Bug???
  template mix(a,b,c,d,e,f,g,h: int32): stmt =
    a = a xor (b shl 11); d += a; b += c
    b = b xor (c shr 2);  e += b; c += d
    c = c xor (d shl 8);  f += c; d += e
    d = d xor (e shr 16); g += d; e += f
    e = e xor (f shl 10); h += e; f += g
    f = f xor (g shr 4);  a += f; g += h
    g = g xor (h shl 8);  b += g; h += a
    h = h xor (a shr 9);  c += h; a += b

  for i in 0..3: # Scramble
    mix(a,b,c,d,e,f,g,h)

  for i in countup(0, isaacSize-1, 8):
    if(useSeed): # Use the seed value in rsl
      a += self.rsl[i  ]; b += self.rsl[i+1]; c += self.rsl[i+2]; d += self.rsl[i+3]
      e += self.rsl[i+4]; f += self.rsl[i+5]; g += self.rsl[i+6]; h += self.rsl[i+7]
    mix(a,b,c,d,e,f,g,h)
    self.mem[i  ] = a; self.mem[i+1] = b; self.mem[i+2] = c; self.mem[i+3] = d
    self.mem[i+4] = e; self.mem[i+5] = f; self.mem[i+6] = g; self.mem[i+7] = h

  if(useSeed): # Second pass to ensure seed affects everything
    for i in countup(0, isaacSize-1, 8):
      a += self.mem[i  ]; b += self.mem[i+1]; c += self.mem[i+2]; d += self.mem[i+3]
      e += self.mem[i+4]; f += self.mem[i+5]; g += self.mem[i+6]; h += self.mem[i+7]
      mix(a,b,c,d,e,f,g,h)
      self.mem[i  ] = a; self.mem[i+1] = b; self.mem[i+2] = c; self.mem[i+3] = d
      self.mem[i+4] = e; self.mem[i+5] = f; self.mem[i+6] = g; self.mem[i+7] = h

  self.refill()
  self.cursor = isaacSize

{.pop.}


proc next32[RNG: PIsaacRng|PIsaacMinusRng](self: RNG): int32 {.inline.} =
  if self.cursor == 0:
    self.refill()
    self.cursor = isaacSize
  dec self.cursor
  return self.rsl[self.cursor]

proc reset*[RNG: PIsaacRng|PIsaacMinusRng, IntType: TInteger
            ](self: var RNG, seed: IntType) {.inline.}
proc reset*[RNG: PIsaacRng|PIsaacMinusRng, IntType: TInteger
            ](self: var RNG, seed: iterator(): IntType {.closure.})

from times import epochTime, cpuTime
proc newRng*(RNG: typedesc[PIsaacRng|PIsaacMinusRng]): RNG =
  ## Create a new ISAAC PRNG using a seed generated from the current time
  ##
  ## This constructor is made for convenience, NOT security
  ## 
  ## NOTE: Creating many RNGs in a short period of time will increase the
  ## likelihood of two RNGs having the same state. Either use only one RNG,
  ## provide an appropriate seed value to an alternate constructor, or wait
  ## a period of time.
  ##
  ## IMPORTANT: If you are considering using this instance for anything
  ## approaching cryptographic purposes, using this constructor is NOT an
  ## appropriate solution. Seeding with a fully TRUE random int32 array of
  ## size isaacSize is ideal. Some form of unpredictable entropy is highly
  ## recommended for cryptographic purposes. That said, heed the warning at
  ## the top of this documentation that this implementation has NOT been
  ## certified for cryptographic purposes regardless.
  ##
  ## Usage:
  ##
  ## .. code-block:: nimrod
  ##   var isaac = newRng(PIsaacRng)
  new(result)
  when sizeof(type(epochTime())) == 4:
    result.reset(cast[int64](epochTime()) xor (cast[int64](cpuTime()) shl 32))
  else:
    result.reset(cast[int64](epochTime()) xor cast[int64](cpuTime()))

proc newRng*[IntType: TInteger
            ](RNG: typedesc[PIsaacRng|PIsaacMinusRng], seed: IntType): RNG =
  ## Create a new ISAAC PRNG using a specified Integral seed value
  ##
  ## This constructor is made for convenience, NOT security
  ##
  ## Usage:
  ##
  ## .. code-block:: nimrod
  ##   var isaac = newRng(PIsaacRng, someSeedValue)
  new(result)
  result.reset(seed)

proc newRng*(RNG: typedesc[PIsaacRng|PIsaacMinusRng],
              seed: iterator(): TInteger {.closure.}): RNG =
  ## Create a new ISAAC PRNG using a specified iterator providing Integers. Only
  ## up to isaacSize 4-byte chunks will be used from the seed, but the larger
  ## the seed up to that number, the better.
  ##
  ## Ideally, you should provide a seed generated from a true random source
  ## (such as bits requested from http://random.org at runtime) for the highest
  ## quality and most unpredictable pseudorandom number generation.
  ##
  ## Usage:
  ##
  ## .. code-block:: nimrod
  ##   var isaac = newRng(PIsaacRng, myTrueRandomIterator)
  new(result)
  result.reset(seed)

proc next*[RNG: PIsaacRng|PIsaacMinusRng
          ](self: RNG, T: typedesc[TInteger]): T {.inline.} =
  ## Get the next integer of specified size from the ISAAC PRNG
  ##
  ## If you want an integer bound to a particular range, use `somethingElse`
  ##
  ## Usage:
  ##
  ## .. code-block:: nimrod
  ##   var a64BitNumber = isaacPrng.next(int64)
  when sizeof(T) == 8:
    return (cast[T](self.next32()) shl 32) or cast[T](ze64(self.next32()))
  else:
    return cast[T](self.next32())

proc reset*[RNG: PIsaacRng|PIsaacMinusRng, IntType: TInteger
            ](self: var RNG, seed: IntType) =
  ## Resets and reseeds the ISAAC PRNG with the provided seed value
  ##
  ## Usage:
  ##
  ## .. code-block:: nimrod
  ##   var isaacPrng = ...
  ##   #... use it for awhile ...
  ##   isaacPrng.reset(myNewUnpredictableSeed)
  iterator repeatSeed(): IntType {.closure.} =
    yield seed
  self.reset(repeatSeed)

proc reset*[RNG: PIsaacRng|PIsaacMinusRng, IntType: TInteger
            ](self: var RNG, seed: iterator(): IntType {.closure.}) =
  ## Similar to the constructor that takes an iterator providing seed value, this
  ## reset can potentially make a very unpredictable state for ISAAC.
  var pos, statePos, storageTop = 0
  var storage: array[isaacSize, int32]
  var r: IntType ## Why do I need this?! The template is {.immediate.}!
  mixin shoveEachTo
  seed.shoveEachTo(r, int32):
    storage[pos] = r
    self.rsl[pos] = r
    pos += 1
    if(pos == isaacSize):
      self.init(true)
      return
  statePos = pos
  storageTop = pos
  # Repeat the pattern until the entire state is filled
  for next in storageTop..isaacSize-1:
    if(pos == storageTop): pos = 0
    self.rsl[next] = storage[pos]
    pos += 1
  self.init(true)

proc remix[RNG: PIsaacRng|PIsaacMinusRng, IntType: TInteger
            ](self: var RNG, seed: iterator(): IntType {.closure.})

proc remix*[RNG: PIsaacRng|PIsaacMinusRng, IntType: TInteger
            ](self: var RNG, seed: IntType) {.inline.} =
  ## Uses the provided seed to "mix" in with the current state. Suggested use:
  ## get entropy somewhere and slowly mix in the entropy as you use the PRNG.
  ##
  ## Usage:
  ##
  ## .. code-block:: nimrod
  ##   var isaacPrng = ...
  ##   #... use it for awhile ...
  ##   isaacPrng.remix(entropyBits)
  iterator repeatSeed(): IntType {.closure.} =
    yield seed
  self.remix(repeatSeed)

proc remix*[RNG: PIsaacRng|PIsaacMinusRng, IntType: TInteger
            ](self: var RNG, seed: iterator(): IntType {.closure.}) =
  ## Similar to the other procedures taking in a seed iterator, this function allows
  ## you to mix in a lot of entropy from any source
  var pos, statePos, storageTop = 0
  var storage: array[isaacSize, int32]
  var r: IntType ## Why do I need this?! The template is {.immediate.}!
  mixin shoveEachTo
  seed.shoveEachTo(r, int32):
    storage[pos] = r
    self.rsl[pos] = self.rsl[pos] xor r
    pos += 1
    if(pos == isaacSize):
      return
  statePos = pos
  storageTop = pos
  # Repeat the pattern until the entire state is filled
  for next in storageTop..isaacSize-1:
    if(pos == storageTop): pos = 0
    self.rsl[next] = self.rsl[next] xor storage[pos]
    pos += 1

when isMainModule: ## Official test to make sure it outputs correct results
  var testIsaacRng = newRng(PIsaacRng, 0)
  var officialOutput = readFile("officialOutput.txt")

  # Strangely, the "official tests" written for ISAAC is ran backwards
  # through the array. This is ONLY to compare with the "official" output
  # It is unknown whether the direction you traverse the array has any effect
  # on the security of the PRNG (although, I suspect not, but know better)
  # Thus, the official "get next" is by-the-books
  proc revNext(self: PIsaacRng): int32 =
    if self.cursor == isaacSize:
      self.refill()
      self.cursor = 0
    result = self.rsl[self.cursor]
    inc self.cursor

  from strutils import toHex, toLower, split
  var i = 0
  for good in officialOutput.split():
    var nextTest = testIsaacRng.revNext().toHex(8).toLower()
    if(nextTest != good):
      stdout.writeln("Item ", i, ": ", nextTest, " != ", good)
      raise newException(ESynch, "Test Failed.")
    inc i

  stdout.writeln("Test Passed.")
