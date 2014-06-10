#
# Ramrod, the Nimrod Random library
# (c) Copyright 2014 Chris Cain (zshazz)
#
# Licensed under MIT (see LICENSE)
#
# file: isaac.nim

## This module hosts some general utility functions needed for Ramrod

import unsigned
template shoveEachTo*[F: TInteger](it: iterator(): F {.closure.}, r: expr,
                    T: typedesc[TInteger], body: stmt) {.immediate.} =
  when sizeof(type(it())) >= sizeof(T):
    const ratio = sizeof(type(it())) div sizeof(T)
    var storage: array[ratio, T]
    for item in it():
      var curr = item
      for cell in low(storage)..high(storage):
        storage[cell] = cast[T](curr)
        curr = curr shr (sizeof(T)*8)
      for cell in countdown(high(storage), low(storage)):
        var r: T = storage[cell]
        body
  else:
    block:
      var cursor = 0
      const ratio = sizeof(T) div sizeof(type(it()))
      var r: T = 0
      for item in it():
        r = r shl cast[T](8*sizeof(type(it())))
        r = r or cast[T](ze64(item))
        inc cursor
        if cursor != ratio:
          continue
        body
        cursor = 0
        r = 0
