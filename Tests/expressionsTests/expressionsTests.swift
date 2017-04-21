import XCTest
import LogicKit
@testable import expressions

class expressionsTests: XCTestCase {

   func testToNumber() {

      print("\n[begin tests]\n")

      let V = Variable(named: "V")
      // let G = Variable(named: "G")
      // let I = Variable(named: "I")
      // let J = Variable(named: "J")
      // let expected : Term = List.cons (Value (5), List.cons (Value (2), List.empty))
      let prob = eval(input: and(t,lessthan(add(toNumber(20),toNumber(2)),subtract(toNumber(27),toNumber(4)))), output: V)
      // var counter = 0
      for sol in solve(prob) {
         print(sol.reified()[V])
         // print(sol.reified()[G])
         // counter += 1
      }
      // print(counter)
      // XCTAssert (toNumber (51).equals (expected), "toNumber is incorrect")

      print("\n[end tests]\n")

   }

   static var allTests : [(String, (expressionsTests) -> () throws -> Void)] {
      return [
         ("testToNumber", testToNumber),
      ]
   }

}
