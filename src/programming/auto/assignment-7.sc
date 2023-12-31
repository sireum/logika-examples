// #Sireum #Logika
//@Logika: --background save
import org.sireum._

var dimes: Z = Z.read()
var money: Z = dimes * 10

assert(money == dimes * 10)

// Say that one more dime shows up:
dimes = dimes + 1

// The amount of money is less that what it should be; fix it:
money = money + 10

// Claim that the invariant has been re-established
assert(money == dimes * 10)