import isaac, well

var isaacPrng = newRng(PIsaacRng)
var wellPrng = newRng(PWell512)

stdout.writeln(isaacPrng.next(int32))
stdout.writeln(wellPrng.next(int32))

# Errors everywhere when used! Great...
# user.nim(3, 22) Info: instantiation from here
# isaac.nim(246, 10) Info: instantiation from here
# isaac.nim(305, 6) Info: instantiation from here
# isaac.nim(314, 6) Error: undeclared identifier: 'shoveEachTo'
