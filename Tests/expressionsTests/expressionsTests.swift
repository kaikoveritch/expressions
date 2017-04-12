import XCTest
import LogicKit
@testable import expressions

class expressionsTests: XCTestCase {

   func testToNumber() {

      print("\n[begin tests]\n")

      let V = Variable(named: "V")
      let G = Variable(named: "G")
      let expected : Term = List.cons (Value (5), List.cons (Value (1), List.empty))
      let prob = sum(expected, toNumber(1), V)
      for sol in solve(prob) {
         print(sol.reified()[V])
      }
      for sol in solve(digit_sum(toNumber(4),toNumber(9),G,V)) {
         print(sol.reified()[V])
         print(sol.reified()[G])
      }
      // XCTAssert (toNumber (51).equals (expected), "toNumber is incorrect")

      print("\n[end tests]\n")

   }

   static var allTests : [(String, (expressionsTests) -> () throws -> Void)] {
      return [
         ("testToNumber", testToNumber),
      ]
   }

}
