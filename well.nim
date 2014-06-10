#
# Ramrod, the Nimrod Random library
# (c) Copyright 2014 Chris Cain (zshazz)
#
# Licensed under MIT (see LICENSE)
#
# file: well.nim

## This module implements the WELL (Well Equidistributed Long-period Linear)
## PRNG. This is similar to MT19937 in many respects, but is supposed to be
## better in many respects.
##
## Despite having a smaller period, WELL512's period of 2^512 would still be
## impossible for any modern computer to traverse (as of this writing).
## This algorithm is appropriate for "NON-SECURE" purposes as it has never been
## advertised as cryptographically secure.
##
## The implementation is based on a public domain C++ example from a paper in
## 2008: http://www.lomont.org/Math/Papers/2008/Lomont_PRNG_2008.pdf

import unsigned, util

const
  well512Number = 0xDA442D24'i32
  well512StateSize* = 16
  ## Number of int32s that make up the WELL512 state
  well512Mask = well512StateSize - 1

type
  PWell512* = ref object
    ## Instance of a WELL512 PRNG
    index: int
    state: array[well512StateSize, int32]

proc init(self: PWell512) =
  ## Fill up self.state with some bits
  ##
  ## Technically, I haven't seen this anywhere, but an empty Well512 only
  ## generates 0s, so this is kind of necessary
  self.index = 0
  for i in low(self.state)..high(self.state):
    self.state[i] = cast[int32](i)

proc checkState(self: PWell512) =
  for item in self.state:
    if item != 0:
      return
  self.init()

proc next32(self: PWell512): int32 =
  template fit(e: expr): expr = (e) and well512Mask
  var a,b,c,d: int32
  a = self.state[self.index]
  c = self.state[fit(self.index+13)]
  b = a xor c xor (a shr 16) xor (c shr 15)
  c = self.state[fit(self.index+9)]
  c = c xor (c shl 11)
  self.state[self.index] = b xor c
  a = self.state[self.index]
  d = a xor ((a shr 5) and well512Number)
  self.index = fit(self.index + 15)
  a = self.state[self.index]
  self.state[self.index] = a xor b xor d xor (a shr 2) xor (b shr 18) xor (c shr 28)
  return self.state[self.index]

proc reset[IntType: TInteger](self: var PWell512, seed: IntType) {.inline.}
proc reset[IntType: TInteger](self: var PWell512, seed: iterator(): IntType {.closure.})

from times import epochTime, cpuTime
proc newRng*(RNG: typedesc[PWell512]): RNG =
  ## Create a new Well512 rng using a seed generated from the current time
  ##
  ## This constructor is made for convenience, but it has some weaknesses
  ## inherent to using the time as a seed
  ## 
  ## NOTE: Creating many RNGs in a short period of time will increase the
  ## likelihood of two RNGs having the same state. Either use only one RNG,
  ## provide an appropriate seed value to an alternate constructor, or wait
  ## a period of time.
  ##
  ## Usage:
  ##
  ## .. code-block:: nimrod
  ##   var wellPrng = newRng(PWell512)
  new(result)
  when sizeof(type(epochTime())) == 4:
    result.reset(cast[int64](epochTime()) xor (cast[int64](cpuTime()) shl 32))
  else:
    result.reset(cast[int64](epochTime()) xor cast[int64](cpuTime()))

proc newRng*[IntType: TInteger](RNG: typedesc[PWell512], seed: IntType): RNG =
  ## Create a new Well512 rng using a specified Integral seed value
  ##
  ## Usage:
  ##
  ## .. code-block:: nimrod
  ##   var wellPrng = newRng(PWell512, 424242)
  new(result)
  result.reset(seed)

proc newRng*(RNG: typedesc[PWell512],
              seed: iterator(): TInteger {.closure.}): RNG =
  ## Create a new Well512 rng using an iterator that provides integral
  ## values. The more integral values it can provide, up to a maximum of
  ## well512StateSize * sizeof(int32) (which is 4), the better and less
  ## predictable the initial state will be.
  ##
  ## Usage:
  ##
  ## .. code-block:: nimrod
  ##   var wellPrng = newRng(PWell512, anIterator)
  new(result)
  result.reset(seed)

proc next*(self: PWell512, T: typedesc[TInteger]): T {.inline.} =
  ## Get the next integer of specified size from the Well512 RNG
  ##
  ## If you want an integer bound to a particular range, use `somethingElse`
  ##
  ## Usage:
  ##
  ## .. code-block:: nimrod
  ##   var a16BitNumber = wellPrng.next(int16)
  when sizeof(T) == 8:
    return (cast[T](self.next32()) shl 32) or cast[T](ze64(self.next32()))
  else:
    return cast[T](self.next32())

proc reset*[IntType: TInteger](self: var PWell512, seed: IntType) =
  ## Resets and reseeds the Well512 RNG with the provided seed value
  ##
  ## Usage:
  ##
  ## .. code-block:: nimrod
  ##   var wellPrng = ...
  ##   #... use it for awhile ...
  ##   wellPrng.reset(myNewUnpredictableSeed)
  iterator repeatSeed(): IntType {.closure.} =
    yield seed
  self.reset(repeatSeed)

proc reset*[IntType: TInteger](self: var PWell512, seed: iterator(): IntType {.closure.}) =
  ## Similar to the constructor that takes an iterator providing seed value, this
  ## reset can potentially make a very unpredictable state for Well512.
  var pos, statePos, storageTop = 0
  var storage: array[len(self.state), int32]
  var r: IntType ## Why do I need this?! The template is {.immediate.}!
  seed.shoveEachTo(r, int32):
    storage[pos] = r
    self.state[pos] = r
    pos += 1
    if(pos == len(self.state)):
      self.checkState()
      return
  statePos = pos
  storageTop = pos
  # Repeat the pattern until the entire state is filled
  for next in storageTop..high(storage):
    if(pos == storageTop): pos = 0
    self.state[next] = storage[pos]
    pos += 1
  self.checkState()

proc remix[IntType: TInteger](self: var PWell512, seed: iterator(): IntType {.closure.})

proc remix*[IntType: TInteger](self: var PWell512, seed: IntType) =
  ## Uses the provided seed to "mix" in with the current state. Suggested use:
  ## get entropy somewhere and slowly mix in the entropy as you use the PRNG.
  ##
  ## Usage:
  ##
  ## .. code-block:: nimrod
  ##   var wellPrng = ...
  ##   #... use it for awhile ...
  ##   wellPrng.remix(entropyBits)
  iterator repeatSeed(): IntType {.closure.} =
    yield seed
  self.remix(repeatSeed)

proc remix*[IntType: TInteger](self: var PWell512, seed: iterator(): IntType {.closure.}) =
  ## Similar to the other procedures taking in a seed iterator, this function allows
  ## you to mix in a lot of entropy from any source
  var pos, statePos, storageTop = 0
  var storage: array[len(self.state), int32]
  var r: IntType
  seed.shoveEachTo(r, int32):
    storage[pos] = r
    self.state[pos] = self.state[pos] xor r
    pos += 1
    if(pos == len(self.state)):
      self.checkState()
      return
  statePos = pos
  storageTop = pos
  # Repeat the pattern until the entire state is filled
  for next in storageTop..high(storage):
    if(pos == storageTop): pos = 0
    self.state[next] = self.state[next] xor storage[pos]
    pos += 1
  self.checkState()

when isMainModule:
  var testWell = newRng(PWell512, 0)

  when true:
    var sum = 0
    for j in 0 .. 4:
      for i in 0 .. (1024 * 1024):
        sum += testWell.next(int)
      testWell.remix(232332)

    stdout.writeln(sum)
  else:
    for i in 0 .. 128:
      stdout.writeln(testWell.next(int32))
