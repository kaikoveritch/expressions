import XCTest
import LogicKit
@testable import expressions

// Wrapper struct and resultsOf function
// Shamefully ripped off from the minotaurTests file in order to test the
// results in a manageable manner.

struct Wrapper : Equatable, CustomStringConvertible {
  let term : Term

  var description: String {
      return "\(self.term)"
  }

  static func ==(lhs: Wrapper, rhs: Wrapper) -> Bool {
    return (lhs.term).equals (rhs.term)
  }

}

func resultsOf (goal: Goal, variables: [Variable]) -> [[Variable: Wrapper]] {
    var result = [[Variable: Wrapper]] ()
    for s in solve (goal) {
        let solution  = s.reified ()
        var subresult = [Variable: Wrapper] ()
        for v in variables {
            subresult [v] = Wrapper (term: solution [v])
        }
        if !result.contains (where: { x in x == subresult }) {
            result.append (subresult)
        }
    }
    return result
}

// Tests

class expressionsTests: XCTestCase {

   // Display for readability
   func startTests() {
      print("\n[Starting tests]\n")
   }

   func testToNumber() {

      let expected : Term = List.cons (Value (5), List.cons (Value (1), List.empty))
      XCTAssert (toNumber (51).equals (expected), "toNumber is incorrect")
   }

   /*=========================== Arithmetic tests ============================*/

   // Testing some sums
   func testSum() {

      let A = Variable(named: "A")

      // 6+3 = 9
      var prob = sum(toNumber(6), toNumber(3), A)
      var results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(9)), "Result is false")

      // 0+728 = 728
      prob = sum(toNumber(0), toNumber(728), A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(728)), "Result is false")

      // 42+101 = 143
      prob = sum(toNumber(42), toNumber(101), A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(143)), "Result is false")

      // 998+2 = 1000
      prob = sum(toNumber(998), toNumber(2), A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(1000)), "Result is false")

      // 193+426 = 619
      prob = sum(toNumber(193), toNumber(426), A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(619)), "Result is false")
   }

   // Testing some subtractions
   func testSub() {

      let A = Variable(named: "A")

      // 7-3 = 4
      var prob = minus(toNumber(7), toNumber(3), A)
      var results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(4)), "Result is false")

      // 42-0 = 42
      prob = minus(toNumber(42), toNumber(0), A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(42)), "Result is false")

      // 2-4 = undef
      prob = minus(toNumber(2), toNumber(4), A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 0, "Number of results is wrong")

      // 100-10 = 90
      prob = minus(toNumber(100), toNumber(10), A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(90)), "Result is false")

      // 31-24 = 7
      prob = minus(toNumber(31), toNumber(24), A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(7)), "Result is false")
   }

   // Testing some products
   func testProd() {

      let A = Variable(named: "A")

      // 9*9 = 81
      var prob = prod(toNumber(9), toNumber(9), A)
      var results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(81)), "Result is false")

      // 1000*0 = 0
      prob = prod(toNumber(1000), toNumber(0), A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(0)), "Result is false")

      // 123*11 = 1353
      prob = prod(toNumber(123), toNumber(11), A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(1353)), "Result is false")
   }

   // Testing some divisions
   func testDiv() {

      let A = Variable(named: "A")

      // 24/6 = 4
      var prob = div(toNumber(24), toNumber(6), A)
      var results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(4)), "Result is false")

      // 13/2 = 6
      prob = div(toNumber(13), toNumber(2), A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(6)), "Result is false")

      // 32/12 = 2
      prob = div(toNumber(32), toNumber(12), A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(2)), "Result is false")
   }

   // Testing the general arithmetic
   func testArithmetic() {

      let A = Variable(named: "A")

      // 193+426 = 619
      var prob = evalArithmetic(input: add(toNumber(193),toNumber(426)), output: A)
      var results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(619)), "Result is false")

      // 7-3 = 4
      prob = evalArithmetic(input: subtract(toNumber(7),toNumber(3)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(4)), "Result is false")

      // 123*11 = 1353
      prob = evalArithmetic(input: multiply(toNumber(123),toNumber(11)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(1353)), "Result is false")

      // 32/12 = 2
      prob = evalArithmetic(input: divide(toNumber(32),toNumber(12)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(2)), "Result is false")
   }

   /*============================== Logic tests ==============================*/

   // Testing general logic
   func testLogic() {

      let A = Variable(named: "A")

      // !f = t
      var prob = evalBoolean(input: not(f), output: A)
      var results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")

      // !t = f
      prob = evalBoolean(input: not(t), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: f), "Result is false")

      // f && f = f
      prob = evalBoolean(input: and(f,f), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: f), "Result is false")

      // f && t = f
      prob = evalBoolean(input: and(f,t), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: f), "Result is false")

      // t && f = f
      prob = evalBoolean(input: and(t,f), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: f), "Result is false")

      // t && t = t
      prob = evalBoolean(input: and(t,t), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")

      // f || f = f
      prob = evalBoolean(input: or(f,f), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: f), "Result is false")

      // f || t = t
      prob = evalBoolean(input: or(f,t), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")

      // t || f = t
      prob = evalBoolean(input: or(t,f), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")

      // t || t = t
      prob = evalBoolean(input: or(t,t), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")

      // f => f = t
      prob = evalBoolean(input: implies(f,f), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")

      // f => t = t
      prob = evalBoolean(input: implies(f,t), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")

      // t => f = f
      prob = evalBoolean(input: implies(t,f), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: f), "Result is false")

      // t => t = t
      prob = evalBoolean(input: implies(t,t), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")
   }

   /*=========================== Comparisons tests ===========================*/

   // Testing some equalities
   func testEquality() {

      // 36 == 36 = true
      var prob = eq(toNumber(36), toNumber(36))
      var results = resultsOf(goal: prob, variables: [])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")

      // 36 == 7 = false
      prob = eq(toNumber(36), toNumber(7))
      results = resultsOf(goal: prob, variables: [])
      XCTAssertEqual(results.count, 0, "Number of results is wrong")
   }

   // Testing some inequalities
   func testInequality() {

      // 36 != 66 = true
      var prob = neq(toNumber(36), toNumber(66))
      var results = resultsOf(goal: prob, variables: [])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")

      // 36 != 367 = true
      prob = neq(toNumber(36), toNumber(367))
      results = resultsOf(goal: prob, variables: [])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")

      // 36 != 36 = false
      prob = neq(toNumber(36), toNumber(36))
      results = resultsOf(goal: prob, variables: [])
      XCTAssertEqual(results.count, 0, "Number of results is wrong")
   }

   // Testing some strict inferiorities
   func testInf() {

      // 14 < 101 = true
      var prob = lt(toNumber(14), toNumber(101))
      var results = resultsOf(goal: prob, variables: [])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")

      // 20 < 8 = false
      prob = lt(toNumber(20), toNumber(8))
      results = resultsOf(goal: prob, variables: [])
      XCTAssertEqual(results.count, 0, "Number of results is wrong")

      // 42 < 42 = false
      prob = lt(toNumber(42), toNumber(42))
      results = resultsOf(goal: prob, variables: [])
      XCTAssertEqual(results.count, 0, "Number of results is wrong")
   }

   // Testing some inferiorities
   func testInfEq() {

      // 14 ≤ 101 = true
      var prob = loet(toNumber(14), toNumber(101))
      var results = resultsOf(goal: prob, variables: [])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")

      // 20 ≤ 8 = false
      prob = loet(toNumber(20), toNumber(8))
      results = resultsOf(goal: prob, variables: [])
      XCTAssertEqual(results.count, 0, "Number of results is wrong")

      // 42 ≤ 42 = true
      prob = loet(toNumber(42), toNumber(42))
      results = resultsOf(goal: prob, variables: [])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
   }

   // Testing general relations
   func testRelations() {

      let A = Variable(named: "A")

      // 12 == 12 = true
      var prob = evalComparison(input: equal(toNumber(12), toNumber(12)), output: A)
      var results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")

      // 12 == 10 = false
      prob = evalComparison(input: equal(toNumber(12), toNumber(10)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: f), "Result is false")

      // 12 != 10 = true
      prob = evalComparison(input: notequal(toNumber(12), toNumber(10)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")

      // 12 != 120 = true
      prob = evalComparison(input: notequal(toNumber(12), toNumber(120)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")

      // 12 != 12 = false
      prob = evalComparison(input: notequal(toNumber(12), toNumber(12)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: f), "Result is false")

      // 9 < 56 = true
      prob = evalComparison(input: lessthan(toNumber(9), toNumber(56)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")

      // 107 < 74 = false
      prob = evalComparison(input: lessthan(toNumber(107), toNumber(74)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: f), "Result is false")

      // 19 < 19 = false
      prob = evalComparison(input: lessthan(toNumber(19), toNumber(19)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: f), "Result is false")

      // 9 ≤ 56 = true
      prob = evalComparison(input: lessequal(toNumber(9), toNumber(56)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")

      // 107 ≤ 74 = false
      prob = evalComparison(input: lessequal(toNumber(107), toNumber(74)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: f), "Result is false")

      // 19 ≤ 19 = true
      prob = evalComparison(input: lessequal(toNumber(19), toNumber(19)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")

      // 9 > 56 = false
      prob = evalComparison(input: greaterthan(toNumber(9), toNumber(56)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: f), "Result is false")

      // 107 > 74 = true
      prob = evalComparison(input: greaterthan(toNumber(107), toNumber(74)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")

      // 19 > 19 = false
      prob = evalComparison(input: greaterthan(toNumber(19), toNumber(19)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: f), "Result is false")

      // 9 ≥ 56 = false
      prob = evalComparison(input: greaterequal(toNumber(9), toNumber(56)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: f), "Result is false")

      // 107 ≥ 74 = true
      prob = evalComparison(input: greaterequal(toNumber(107), toNumber(74)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")

      // 19 ≥ 19 = true
      prob = evalComparison(input: greaterequal(toNumber(19), toNumber(19)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")
   }

   /*======================= General evaluation tests ========================*/

   // Test some composed arithmetic
   func testComposedArithmetic() {

      let A = Variable(named: "A")

      // (10*(10-2))+(14/11) = 81
      var prob = eval(input: add(multiply(toNumber(10), subtract(toNumber(10), toNumber(2))), divide(toNumber(14), toNumber(11))), output: A)
      var results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(81)), "Result is false")

      // (100-(7*(3+4))) = 51
      prob = eval(input: subtract(toNumber(100), multiply(toNumber(7), add(toNumber(3), toNumber(4)))), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: toNumber(51)), "Result is false")
   }

   // Test some composed logic
   func testComposedLogic() {

      let A = Variable(named: "A")

      // t => ((not f) or (f and t)) = t
      var prob = eval(input: implies(t, or(not(f), and(f, t))), output: A)
      var results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")

      // not(not(f)) or ((t and t) => f) = f
      prob = eval(input: or(not(not(f)), implies(and(t, t), f)), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: f), "Result is false")
   }

   // Test everything together
   func testMixedEvaluation() {

      let A = Variable(named: "A")

      // t and ((20+2) < (27-4)) = t
      var prob = eval(input: and(t,lessthan(add(toNumber(20),toNumber(2)),subtract(toNumber(27),toNumber(4)))), output: A)
      var results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: t), "Result is false")

      // (f or 26 != 269) => ((30-15) ≥ 16) = f
      prob = eval(input: implies(or(f, notequal(toNumber(26), toNumber(269))), greaterequal(subtract(toNumber(30), toNumber(15)), toNumber(16))), output: A)
      results = resultsOf(goal: prob, variables: [A])
      XCTAssertEqual(results.count, 1, "Number of results is wrong")
      XCTAssertEqual(Array<Dictionary<Variable, Wrapper>>(results)[0][A]!, Wrapper(term: f), "Result is false")
   }

   // Display for readability
   func endTests() {
      print("\n[End of tests]\n")
   }

   static var allTests : [(String, (expressionsTests) -> () throws -> Void)] {
      return [
         ("startTests", startTests),
         ("testToNumber", testToNumber),
         ("testSum", testSum),
         ("testSub", testSub),
         ("testProd", testProd),
         ("testDiv", testDiv),
         ("testArithmetic", testArithmetic),
         ("testLogic", testLogic),
         ("testEquality", testEquality),
         ("testInequality", testInequality),
         ("testInf", testInf),
         ("testInfEq", testInfEq),
         ("testRelations", testRelations),
         ("testComposedArithmetic", testComposedArithmetic),
         ("testComposedLogic", testComposedLogic),
         ("testMixedEvaluation", testMixedEvaluation),
         ("endTests", endTests),
      ]
   }

}
