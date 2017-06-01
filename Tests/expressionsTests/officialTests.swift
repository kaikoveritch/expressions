import XCTest
import LogicKit
@testable import expressions

class officialTests: XCTestCase {

  func testOfficialAddition_1 () {
    let result = Variable (named: "v")
    let goal   = evalArithmetic (input: add (toNumber(999), toNumber(0)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (toNumber (999+0)), "official addition 1 fails")
      break
    }
  }

  func testOfficialAddition_2 () {
    let result = Variable (named: "v")
    let goal   = evalArithmetic (input: add (toNumber(999), toNumber(999)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (toNumber (999+999)), "official addition 2 fails")
      break
    }
  }

  func testOfficialSubtraction_1 () {
    let result = Variable (named: "v")
    let goal   = evalArithmetic (input: subtract (toNumber(20), toNumber(9)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (toNumber (20-9)), "official subtraction 1 fails")
      break
    }
  }

  func testOfficialSubtraction_2 () {
    let result = Variable (named: "v")
    let goal   = evalArithmetic (input: subtract (toNumber(10), toNumber(0)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (toNumber (10-0)), "official subtraction 2 fails")
      break
    }
  }

  // func testOfficialSubtraction_3 () {
  //   let result   = Variable (named: "v")
  //   let goal     = evalArithmetic (input: subtract (toNumber(0), toNumber(9)), output: result)
  // }

  func testOfficialMultiplication_1 () {
    let result = Variable (named: "v")
    let goal   = evalArithmetic (input: multiply (toNumber(19), toNumber(0)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (toNumber (19*0)), "official multiplication 1 fails")
      break
    }
  }

  func testOfficialMultiplication_2 () {
    let result = Variable (named: "v")
    let goal   = evalArithmetic (input: multiply (toNumber(19), toNumber(1)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (toNumber (19*1)), "official multiplication 2 fails")
      break
    }
  }

  func testOfficialMultiplication_3 () {
    let result = Variable (named: "v")
    let goal   = evalArithmetic (input: multiply (toNumber(19), toNumber(9)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (toNumber (19*9)), "official multiplication 3 fails")
      break
    }
  }

  func testOfficialDivision_1 () {
    let result = Variable (named: "v")
    let goal   = evalArithmetic (input: divide (toNumber(5), toNumber(1)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (toNumber (5/1)), "official division fails")
      break
    }
  }

  // func testOfficialDivision_2 () {
  //   let result = Variable (named: "v")
  //   let goal   = evalArithmetic (input: divide (toNumber(50), toNumber(20)), output: result)
  //   for sub in solve (goal) {
  //     XCTAssert (sub.reified () [result].equals (toNumber (50/20)), "official division fails")
  //     break
  //   }
  // }
  //
  // func testOfficialDivision_3 () {
  //   let result = Variable (named: "v")
  //   let goal   = evalArithmetic (input: divide (toNumber(1), toNumber(0)), output: result)
  // }

  func testOfficialConjunction_1 () {
    let result = Variable (named: "v")
    let goal   = evalBoolean (input: and (t, and (t, t)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (t), "official conjunction fails")
      break
    }
  }

  func testOfficialConjunction_2 () {
    let result = Variable (named: "v")
    let goal   = evalBoolean (input: and (t, and (t, f)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (f), "official conjunction fails")
      break
    }
  }

  func testOfficialConjunction_3 () {
    let result = Variable (named: "v")
    let goal   = evalBoolean (input: and (and (f, t), t), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (f), "official conjunction fails")
      break
    }
  }

  func testOfficialDisjunction_1 () {
    let result = Variable (named: "v")
    let goal   = evalBoolean (input: or (f, or (t, f)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (t), "official disjunction fails")
      break
    }
  }

  func testOfficialDisjunction_2 () {
    let result = Variable (named: "v")
    let goal   = evalBoolean (input: or (f, or (f, f)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (f), "official disjunction fails")
      break
    }
  }

  func testOfficialDisjunction_3 () {
    let result = Variable (named: "v")
    let goal   = evalBoolean (input: or (or (f, f), f), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (f), "official disjunction fails")
      break
    }
  }

  func testOfficialNegation_1 () {
    let result = Variable (named: "v")
    let goal   = evalBoolean (input: not (or (t, f)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (f), "official negation fails")
      break
    }
  }

  func testOfficialNegation_2 () {
    let result = Variable (named: "v")
    let goal   = evalBoolean (input: not (and (t, f)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (t), "official negation fails")
      break
    }
  }

  func testOfficialImplication_1 () {
    let result = Variable (named: "v")
    let goal   = evalBoolean (input: implies (f, f), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (t), "official implication fails")
      break
    }
  }

  func testOfficialImplication_2 () {
    let result = Variable (named: "v")
    let goal   = evalBoolean (input: implies (t, t), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (t), "official implication fails")
      break
    }
  }

  func testOfficialImplication_3 () {
    let result = Variable (named: "v")
    let goal   = evalBoolean (input: implies (t, f), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (f), "official implication fails")
      break
    }
  }

  func testOfficialEquality_1 () {
    let result = Variable (named: "v")
    let goal   = evalComparison (input: equal (toNumber (42), toNumber (42)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (t), "official equality fails")
      break
    }
  }

  func testOfficialEquality_2 () {
    let result = Variable (named: "v")
    let goal   = evalComparison (input: equal (toNumber (42), toNumber (51)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (f), "official equality fails")
      break
    }
  }

  func testOfficialInequality_1 () {
    let result = Variable (named: "v")
    let goal   = evalComparison (input: notequal (toNumber (42), toNumber (42)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (f), "official inequality fails")
      break
    }
  }

  func testOfficialInequality_2 () {
    let result = Variable (named: "v")
    let goal   = evalComparison (input: notequal (toNumber (42), toNumber (51)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (t), "official inequality fails")
      break
    }
  }

  func testOfficialGreaterthan_1 () {
    let result = Variable (named: "v")
    let goal   = evalComparison (input: greaterthan (toNumber (51), toNumber (42)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (t), "official greater than comparison fails")
      break
    }
  }

  func testOfficialGreaterthan_2 () {
    let result = Variable (named: "v")
    let goal   = evalComparison (input: greaterthan (toNumber (42), toNumber (42)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (f), "official greater than comparison fails")
      break
    }
  }

  func testOfficialGreaterthan_3 () {
    let result = Variable (named: "v")
    let goal   = evalComparison (input: greaterthan (toNumber (42), toNumber (51)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (f), "official greater than comparison fails")
      break
    }
  }

  func testOfficialGreaterequal_1 () {
    let result = Variable (named: "v")
    let goal   = evalComparison (input: greaterequal (toNumber (51), toNumber (42)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (t), "official greater or equal comparison fails")
      break
    }
  }

  func testOfficialGreaterequal_2 () {
    let result = Variable (named: "v")
    let goal   = evalComparison (input: greaterequal (toNumber (42), toNumber (42)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (t), "official greater or equal comparison fails")
      break
    }
  }

  func testOfficialGreaterequal_3 () {
    let result = Variable (named: "v")
    let goal   = evalComparison (input: greaterequal (toNumber (42), toNumber (51)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (f), "official greater or equal comparison fails")
      break
    }
  }

  func testOfficialLessthan_1 () {
    let result = Variable (named: "v")
    let goal   = evalComparison (input: lessthan (toNumber (51), toNumber (42)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (f), "official less than comparison fails")
      break
    }
  }

  func testOfficialLessthan_2 () {
    let result = Variable (named: "v")
    let goal   = evalComparison (input: lessthan (toNumber (42), toNumber (42)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (f), "official less than comparison fails")
      break
    }
  }

  func testOfficialLessthan_3 () {
    let result = Variable (named: "v")
    let goal   = evalComparison (input: lessthan (toNumber (42), toNumber (51)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (t), "official less than comparison fails")
      break
    }
  }

  func testOfficialLessequal_1 () {
    let result = Variable (named: "v")
    let goal   = evalComparison (input: lessequal (toNumber (51), toNumber (42)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (f), "official less or equal comparison fails")
      break
    }
  }

  func testOfficialLessequal_2 () {
    let result = Variable (named: "v")
    let goal   = evalComparison (input: lessequal (toNumber (42), toNumber (42)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (t), "official less or equal comparison fails")
      break
    }
  }

  func testOfficialLessequal_3 () {
    let result = Variable (named: "v")
    let goal   = evalComparison (input: lessequal (toNumber (42), toNumber (51)), output: result)
    for sub in solve (goal) {
      XCTAssert (sub.reified () [result].equals (t), "official less or equal comparison fails")
      break
    }
  }

  static var allTests : [(String, (officialTests) -> () throws -> Void)] {
    return [
      ("testOfficialAddition_1"       , testOfficialAddition_1),
      ("testOfficialAddition_2"       , testOfficialAddition_2),
      ("testOfficialSubtraction_1"    , testOfficialSubtraction_1),
      ("testOfficialSubtraction_2"    , testOfficialSubtraction_2),
      // ("testOfficialSubtraction_3"    , testOfficialSubtraction_3),
      ("testOfficialMultiplication_1" , testOfficialMultiplication_1),
      ("testOfficialMultiplication_2" , testOfficialMultiplication_2),
      ("testOfficialMultiplication_3" , testOfficialMultiplication_3),
      ("testOfficialDivision_1"       , testOfficialDivision_1),
      // ("testOfficialDivision_2"       , testOfficialDivision_2),
      // ("testOfficialDivision_3"       , testOfficialDivision_3),
      ("testOfficialConjunction_1"    , testOfficialConjunction_1),
      ("testOfficialConjunction_2"    , testOfficialConjunction_2),
      ("testOfficialConjunction_3"    , testOfficialConjunction_3),
      ("testOfficialDisjunction_1"    , testOfficialDisjunction_1),
      ("testOfficialDisjunction_2"    , testOfficialDisjunction_2),
      ("testOfficialDisjunction_3"    , testOfficialDisjunction_3),
      ("testOfficialNegation_1"       , testOfficialNegation_1),
      ("testOfficialNegation_2"       , testOfficialNegation_2),
      ("testOfficialImplication_1"    , testOfficialImplication_1),
      ("testOfficialImplication_2"    , testOfficialImplication_2),
      ("testOfficialImplication_3"    , testOfficialImplication_3),
      ("testOfficialEquality_1"       , testOfficialEquality_1),
      ("testOfficialEquality_2"       , testOfficialEquality_2),
      ("testOfficialInequality_1"     , testOfficialInequality_1),
      ("testOfficialInequality_2"     , testOfficialInequality_2),
      ("testOfficialGreaterthan_1"    , testOfficialGreaterthan_1),
      ("testOfficialGreaterthan_2"    , testOfficialGreaterthan_2),
      ("testOfficialGreaterthan_3"    , testOfficialGreaterthan_3),
      ("testOfficialGreaterequal_1"   , testOfficialGreaterequal_1),
      ("testOfficialGreaterequal_2"   , testOfficialGreaterequal_2),
      ("testOfficialGreaterequal_3"   , testOfficialGreaterequal_3),
      ("testOfficialLessthan_1"       , testOfficialLessthan_1),
      ("testOfficialLessthan_2"       , testOfficialLessthan_2),
      ("testOfficialLessthan_3"       , testOfficialLessthan_3),
      ("testOfficialLessequal_1"      , testOfficialLessequal_1),
      ("testOfficialLessequal_2"      , testOfficialLessequal_2),
      ("testOfficialLessequal_3"      , testOfficialLessequal_3),
    ]
  }

}
