import LogicKit

/* Information:
 * Digits is self-explanatory
 * EA is the set of all arithmetic expressions
 * EB is the set of all boolean expressions
 * R is the set of all relations
 *
 * ';' denotes a construction of a list (uppercase) and an element (lowercase)
 * nil == List.empty
 */

// This is a utility function, not linked directly to the syntax or the semantic
func reverse_aux (_ L: Term, _ R: Term, _ A: Term) -> Goal { // A is the accumulator
   return
      // If L is empty, the reversal is over and R takes the value of the accumulator
      (L === List.empty && R === A)
      ||
      // Otherwise, the function is called recursively with the first element of
      // L extracted and added to the accumulator (R stays untouched)
      (
         fresh{el in fresh{H in
            L === List.cons(el, H)
            &&
            delayed(reverse_aux (H, R, List.cons(el,A)))
         }}
      )
}
func reverse (_ L: Term, _ R: Term) -> Goal { // L is the original list, R the reversed one
   return
      // Call the auxiliary with an empty accumulator
      reverse_aux (L, R, List.empty)
}

//==============================================================================
// Syntax:
//==============================================================================

// Numbers:

// d in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
// -----------------------------------
// d in Digits
let d0 = Value (0)
let d1 = Value (1)
let d2 = Value (2)
let d3 = Value (3)
let d4 = Value (4)
let d5 = Value (5)
let d6 = Value (6)
let d7 = Value (7)
let d8 = Value (8)
let d9 = Value (9)

// Tests if a term is a digit
func isdigit (_ d: Term) -> Goal {
   return
      d === d0 ||
      d === d1 ||
      d === d2 ||
      d === d3 ||
      d === d4 ||
      d === d5 ||
      d === d6 ||
      d === d7 ||
      d === d8 ||
      d === d9
}

// d in Digits
// -------------------
// d;nil in EA
//
// d in Digits, N in EA
// --------------------
// d;N in EA
func toNumber (_ n : Int) -> Term {
    var result = List.empty
    for char in String (n).characters.reversed () {
        switch char {
        case "0":
            result = List.cons (d0, result)
        case "1":
            result = List.cons (d1, result)
        case "2":
            result = List.cons (d2, result)
        case "3":
            result = List.cons (d3, result)
        case "4":
            result = List.cons (d4, result)
        case "5":
            result = List.cons (d5, result)
        case "6":
            result = List.cons (d6, result)
        case "7":
            result = List.cons (d7, result)
        case "8":
            result = List.cons (d8, result)
        case "9":
            result = List.cons (d9, result)
        default:
            assert (false)
        }
    }
    return result
}

// Checks if a term has the form of a number, nil not included
func isnumber (_ n: Term) -> Goal {
   return   fresh{d in fresh{L in
               n === List.cons(d,L) && isdigit(d)
            }}
}

// Arithmetic:

// lhs,rhs in EA
// ------------------
// add(lhs,rhs) in EA
func add (_ lhs: Term, _ rhs: Term) -> Map {
    return [
      "op"  : Value("+"),
      "lhs" : lhs,
      "rhs" : rhs
   ]
}

// lhs,rhs in EA
// -----------------------
// subtract(lhs,rhs) in EA
func subtract (_ lhs: Term, _ rhs: Term) -> Map {
   return [
     "op"  : Value("-"),
     "lhs" : lhs,
     "rhs" : rhs
  ]
}

// lhs,rhs in EA
// -----------------------
// multiply(lhs,rhs) in EA
func multiply (_ lhs: Term, _ rhs: Term) -> Map {
   return [
     "op"  : Value("*"),
     "lhs" : lhs,
     "rhs" : rhs
  ]
}

// lhs,rhs in EA
// ---------------------
// divide(lhs,rhs) in EA
func divide (_ lhs: Term, _ rhs: Term) -> Map {
   return [
     "op"  : Value("/"),
     "lhs" : lhs,
     "rhs" : rhs
  ]
}

// Booleans:

// b in {true, false}
// ------------------
// b in EB
let t = Value (true)
let f = Value (false)

// b in EB
// ------------
// not(b) in EB
func not (_ of: Term) -> Map {
   return [
    "op"  : Value("¬"),
    "of" : of
   ]
}

// b,c in EB
// --------------
// and(b,c) in EB
func and (_ lhs: Term, _ rhs: Term) -> Map {
   return [
     "op"  : Value("∧"),
     "lhs" : lhs,
     "rhs" : rhs
  ]
}

// b,c in EB
// -------------
// or(b,c) in EB
func or (_ lhs: Term, _ rhs: Term) -> Map {
   return [
    "op"  : Value("∨"),
    "lhs" : lhs,
    "rhs" : rhs
 ]
}

// b,c in EB
// ------------------
// implies(b,c) in EB
func implies (_ lhs: Term, _ rhs: Term) -> Map {
   return [
    "op"  : Value("=>"),
    "lhs" : lhs,
    "rhs" : rhs
 ]
}

// Comparisons:

// n,m in EA
// ------------------
// lessthan(n,m) in R
func lessthan (_ lhs: Term, _ rhs: Term) -> Map {
   return [
    "op"  : Value("<"),
    "lhs" : lhs,
    "rhs" : rhs
 ]
}

// n,m in EA
// -------------------
// lessequal(n,m) in R
func lessequal (_ lhs: Term, _ rhs: Term) -> Map {
   return [
    "op"  : Value("≤"),
    "lhs" : lhs,
    "rhs" : rhs
 ]
}

// n,m in EA
// ---------------------
// greaterthan(n,m) in R
func greaterthan (_ lhs: Term, _ rhs: Term) -> Map {
   return [
    "op"  : Value(">"),
    "lhs" : lhs,
    "rhs" : rhs
 ]
}

// n,m in EA
// ----------------------
// greaterequal(n,m) in R
func greaterequal (_ lhs: Term, _ rhs: Term) -> Map {
   return [
    "op"  : Value("≥"),
    "lhs" : lhs,
    "rhs" : rhs
 ]
}

// n,m in EA
// ---------------
// equal(n,m) in R
func equal (_ lhs: Term, _ rhs: Term) -> Map {
   return [
    "op"  : Value("=="),
    "lhs" : lhs,
    "rhs" : rhs
 ]
}

// n,m in EA
// ------------------
// notequal(n,m) in R
func notequal (_ lhs: Term, _ rhs: Term) -> Map {
   return [
    "op"  : Value("!="),
    "lhs" : lhs,
    "rhs" : rhs
 ]
}

//==============================================================================
// Evaluation:
//==============================================================================
// The specialized evaluations (for an operation, or a category) always work
// supposing that its operands are already evaluated. The evaluation of the
// operands is made in the general eval function in order to conserve flexibility.
// (for instance, a boolean in a logic operation might be gotten from a Relation
// evaluation and not from evalBoolean.)

/********************************* Arithmetic *********************************/

// Give the sum of all pairs of digits as a pair of numbers: (result, carry)
func digit_sum (_ lhs: Term, _ rhs: Term, _ ans: Term, _ carry: Term) -> Goal {
   return
      /********************************* 0+x **********************************/
      // --------------------
      // sum(d0,d) -EA-> 0;d
      (lhs === toNumber(0) && ans === rhs && carry === toNumber(0))
      ||
      /********************************* 1+x **********************************/
      // ----------------------
      // sum(d1,d0) -EA-> 0;1
      (lhs === toNumber(1) && rhs === toNumber(0) && ans === toNumber(1) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d1,d1) -EA-> 0;2
      (lhs === toNumber(1) && rhs === toNumber(1) && ans === toNumber(2) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d1,d2) -EA-> 0;3
      (lhs === toNumber(1) && rhs === toNumber(2) && ans === toNumber(3) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d1,d3) -EA-> 0;4
      (lhs === toNumber(1) && rhs === toNumber(3) && ans === toNumber(4) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d1,d4) -EA-> 0;5
      (lhs === toNumber(1) && rhs === toNumber(4) && ans === toNumber(5) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d1,d5) -EA-> 0;6
      (lhs === toNumber(1) && rhs === toNumber(5) && ans === toNumber(6) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d1,d6) -EA-> 0;7
      (lhs === toNumber(1) && rhs === toNumber(6) && ans === toNumber(7) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d1,d7) -EA-> 0;8
      (lhs === toNumber(1) && rhs === toNumber(7) && ans === toNumber(8) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d1,d8) -EA-> 0;9
      (lhs === toNumber(1) && rhs === toNumber(8) && ans === toNumber(9) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d1,d9) -EA-> 1;0
      (lhs === toNumber(1) && rhs === toNumber(9) && ans === toNumber(0) && carry === toNumber(1))
      ||
      /********************************* 2+x **********************************/
      // ----------------------
      // sum(d2,d0) -EA-> 0;2
      (lhs === toNumber(2) && rhs === toNumber(0) && ans === toNumber(2) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d2,d1) -EA-> 0;3
      (lhs === toNumber(2) && rhs === toNumber(1) && ans === toNumber(3) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d2,d2) -EA-> 0;4
      (lhs === toNumber(2) && rhs === toNumber(2) && ans === toNumber(4) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d2,d3) -EA-> 0;5
      (lhs === toNumber(2) && rhs === toNumber(3) && ans === toNumber(5) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d2,d4) -EA-> 0;6
      (lhs === toNumber(2) && rhs === toNumber(4) && ans === toNumber(6) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d2,d5) -EA-> 0;7
      (lhs === toNumber(2) && rhs === toNumber(5) && ans === toNumber(7) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d2,d6) -EA-> 0;8
      (lhs === toNumber(2) && rhs === toNumber(6) && ans === toNumber(8) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d2,d7) -EA-> 0;9
      (lhs === toNumber(2) && rhs === toNumber(7) && ans === toNumber(9) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d2,d8) -EA-> 1;0
      (lhs === toNumber(2) && rhs === toNumber(8) && ans === toNumber(0) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d2,d9) -EA-> 1;1
      (lhs === toNumber(2) && rhs === toNumber(9) && ans === toNumber(1) && carry === toNumber(1))
      ||
      /********************************* 3+x **********************************/
      // ----------------------
      // sum(d3,d0) -EA-> 0;3
      (lhs === toNumber(3) && rhs === toNumber(0) && ans === toNumber(3) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d3,d1) -EA-> 0;4
      (lhs === toNumber(3) && rhs === toNumber(1) && ans === toNumber(4) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d3,d2) -EA-> 0;5
      (lhs === toNumber(3) && rhs === toNumber(2) && ans === toNumber(5) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d3,d3) -EA-> 0;6
      (lhs === toNumber(3) && rhs === toNumber(3) && ans === toNumber(6) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d3,d4) -EA-> 0;7
      (lhs === toNumber(3) && rhs === toNumber(4) && ans === toNumber(7) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d3,d5) -EA-> 0;8
      (lhs === toNumber(3) && rhs === toNumber(5) && ans === toNumber(8) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d3,d6) -EA-> 0;9
      (lhs === toNumber(3) && rhs === toNumber(6) && ans === toNumber(9) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d3,d7) -EA-> 1;0
      (lhs === toNumber(3) && rhs === toNumber(7) && ans === toNumber(0) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d3,d8) -EA-> 1;1
      (lhs === toNumber(3) && rhs === toNumber(8) && ans === toNumber(1) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d3,d9) -EA-> 1;2
      (lhs === toNumber(3) && rhs === toNumber(9) && ans === toNumber(2) && carry === toNumber(1))
      ||
      /********************************* 4+x **********************************/
      // ----------------------
      // sum(d4,d0) -EA-> 0;4
      (lhs === toNumber(4) && rhs === toNumber(0) && ans === toNumber(4) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d4,d1) -EA-> 0;5
      (lhs === toNumber(4) && rhs === toNumber(1) && ans === toNumber(5) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d4,d2) -EA-> 0;6
      (lhs === toNumber(4) && rhs === toNumber(2) && ans === toNumber(6) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d4,d3) -EA-> 0;7
      (lhs === toNumber(4) && rhs === toNumber(3) && ans === toNumber(7) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d4,d4) -EA-> 0;8
      (lhs === toNumber(4) && rhs === toNumber(4) && ans === toNumber(8) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d4,d5) -EA-> 0;9
      (lhs === toNumber(4) && rhs === toNumber(5) && ans === toNumber(9) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d4,d6) -EA-> 1;0
      (lhs === toNumber(4) && rhs === toNumber(6) && ans === toNumber(0) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d4,d7) -EA-> 1;1
      (lhs === toNumber(4) && rhs === toNumber(7) && ans === toNumber(1) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d4,d8) -EA-> 1;2
      (lhs === toNumber(4) && rhs === toNumber(8) && ans === toNumber(2) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d4,d9) -EA-> 1;3
      (lhs === toNumber(4) && rhs === toNumber(9) && ans === toNumber(3) && carry === toNumber(1))
      ||
      /********************************* 5+x **********************************/
      // ----------------------
      // sum(d5,d0) -EA-> 0;5
      (lhs === toNumber(5) && rhs === toNumber(0) && ans === toNumber(5) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d5,d1) -EA-> 0;6
      (lhs === toNumber(5) && rhs === toNumber(1) && ans === toNumber(6) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d5,d2) -EA-> 0;7
      (lhs === toNumber(5) && rhs === toNumber(2) && ans === toNumber(7) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d5,d3) -EA-> 0;8
      (lhs === toNumber(5) && rhs === toNumber(3) && ans === toNumber(8) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d5,d4) -EA-> 0;9
      (lhs === toNumber(5) && rhs === toNumber(4) && ans === toNumber(9) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d5,d5) -EA-> 1;0
      (lhs === toNumber(5) && rhs === toNumber(5) && ans === toNumber(0) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d5,d6) -EA-> 1;1
      (lhs === toNumber(5) && rhs === toNumber(6) && ans === toNumber(1) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d5,d7) -EA-> 1;2
      (lhs === toNumber(5) && rhs === toNumber(7) && ans === toNumber(2) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d5,d8) -EA-> 1;3
      (lhs === toNumber(5) && rhs === toNumber(8) && ans === toNumber(3) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d5,d9) -EA-> 1;4
      (lhs === toNumber(5) && rhs === toNumber(9) && ans === toNumber(4) && carry === toNumber(1))
      ||
      /********************************* 6+x **********************************/
      // ----------------------
      // sum(d6,d0) -EA-> 0;6
      (lhs === toNumber(6) && rhs === toNumber(0) && ans === toNumber(6) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d6,d1) -EA-> 0;7
      (lhs === toNumber(6) && rhs === toNumber(1) && ans === toNumber(7) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d6,d2) -EA-> 0;8
      (lhs === toNumber(6) && rhs === toNumber(2) && ans === toNumber(8) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d6,d3) -EA-> 0;9
      (lhs === toNumber(6) && rhs === toNumber(3) && ans === toNumber(9) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d6,d4) -EA-> 1;0
      (lhs === toNumber(6) && rhs === toNumber(4) && ans === toNumber(0) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d6,d5) -EA-> 1;1
      (lhs === toNumber(6) && rhs === toNumber(5) && ans === toNumber(1) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d6,d6) -EA-> 1;2
      (lhs === toNumber(6) && rhs === toNumber(6) && ans === toNumber(2) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d6,d7) -EA-> 1;3
      (lhs === toNumber(6) && rhs === toNumber(7) && ans === toNumber(3) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d6,d8) -EA-> 1;4
      (lhs === toNumber(6) && rhs === toNumber(8) && ans === toNumber(4) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d6,d9) -EA-> 1;5
      (lhs === toNumber(6) && rhs === toNumber(9) && ans === toNumber(5) && carry === toNumber(1))
      ||
      /********************************* 7+x **********************************/
      // ----------------------
      // sum(d7,d0) -EA-> 0;7
      (lhs === toNumber(7) && rhs === toNumber(0) && ans === toNumber(7) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d7,d1) -EA-> 0;8
      (lhs === toNumber(7) && rhs === toNumber(1) && ans === toNumber(8) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d7,d2) -EA-> 0;9
      (lhs === toNumber(7) && rhs === toNumber(2) && ans === toNumber(9) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d7,d3) -EA-> 1;0
      (lhs === toNumber(7) && rhs === toNumber(3) && ans === toNumber(0) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d7,d4) -EA-> 1;1
      (lhs === toNumber(7) && rhs === toNumber(4) && ans === toNumber(1) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d7,d5) -EA-> 1;2
      (lhs === toNumber(7) && rhs === toNumber(5) && ans === toNumber(2) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d7,d6) -EA-> 1;3
      (lhs === toNumber(7) && rhs === toNumber(6) && ans === toNumber(3) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d7,d7) -EA-> 1;4
      (lhs === toNumber(7) && rhs === toNumber(7) && ans === toNumber(4) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d7,d8) -EA-> 1;5
      (lhs === toNumber(7) && rhs === toNumber(8) && ans === toNumber(5) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d7,d9) -EA-> 1;6
      (lhs === toNumber(7) && rhs === toNumber(9) && ans === toNumber(6) && carry === toNumber(1))
      ||
      /********************************* 8+x **********************************/
      // ----------------------
      // sum(d8,d0) -EA-> 0;8
      (lhs === toNumber(8) && rhs === toNumber(0) && ans === toNumber(8) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d8,d1) -EA-> 0;9
      (lhs === toNumber(8) && rhs === toNumber(1) && ans === toNumber(9) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d8,d2) -EA-> 1;0
      (lhs === toNumber(8) && rhs === toNumber(2) && ans === toNumber(0) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d8,d3) -EA-> 1;1
      (lhs === toNumber(8) && rhs === toNumber(3) && ans === toNumber(1) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d8,d4) -EA-> 1;2
      (lhs === toNumber(8) && rhs === toNumber(4) && ans === toNumber(2) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d8,d5) -EA-> 1;3
      (lhs === toNumber(8) && rhs === toNumber(5) && ans === toNumber(3) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d8,d6) -EA-> 1;4
      (lhs === toNumber(8) && rhs === toNumber(6) && ans === toNumber(4) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d8,d7) -EA-> 1;5
      (lhs === toNumber(8) && rhs === toNumber(7) && ans === toNumber(5) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d8,d8) -EA-> 1;6
      (lhs === toNumber(8) && rhs === toNumber(8) && ans === toNumber(6) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d8,d9) -EA-> 1;7
      (lhs === toNumber(8) && rhs === toNumber(9) && ans === toNumber(7) && carry === toNumber(1))
      ||
      /********************************* 9+x **********************************/
      // ----------------------
      // sum(d9,d0) -EA-> 0;9
      (lhs === toNumber(9) && rhs === toNumber(0) && ans === toNumber(9) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d9,d1) -EA-> 1;0
      (lhs === toNumber(9) && rhs === toNumber(1) && ans === toNumber(0) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d9,d2) -EA-> 1;1
      (lhs === toNumber(9) && rhs === toNumber(2) && ans === toNumber(1) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d9,d3) -EA-> 1;2
      (lhs === toNumber(9) && rhs === toNumber(3) && ans === toNumber(2) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d9,d4) -EA-> 1;3
      (lhs === toNumber(9) && rhs === toNumber(4) && ans === toNumber(3) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d9,d5) -EA-> 1;4
      (lhs === toNumber(9) && rhs === toNumber(5) && ans === toNumber(4) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d9,d6) -EA-> 1;5
      (lhs === toNumber(9) && rhs === toNumber(6) && ans === toNumber(5) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d9,d7) -EA-> 1;6
      (lhs === toNumber(9) && rhs === toNumber(7) && ans === toNumber(6) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d9,d8) -EA-> 1;7
      (lhs === toNumber(9) && rhs === toNumber(8) && ans === toNumber(7) && carry === toNumber(1))
      ||
      // ----------------------
      // sum(d9,d9) -EA-> 1;8
      (lhs === toNumber(9) && rhs === toNumber(9) && ans === toNumber(8) && carry === toNumber(1))
}

// Auxiliary function to sum.
// temp serves as an accumulator for the digits as they are computed (is reversed !)
func sum_aux (_ lhs: Term, _ rhs: Term, _ ans: Term, _ temp: Term) -> Goal {
   return
      // If both numbers are nil, the sum is done
      //
      // lhs -EA-> nil, rhs -EA-> nil
      // ----------------------------
      // sum(lhs,rhs) -EA-> nil
      (lhs === List.empty && rhs === List.empty && ans === temp)
      ||
      // If one of the numbers is nil, we extract the other's least significant
      // digit and put it in the accumulator to call sum_aux recursively (this)
      // preserves the (reversed) order.
      //
      // lhs -EA-> H;u, rhs -EA-> nil
      // ----------------------------
      // sum(lhs,rhs) -EA-> H;u
      (fresh{u in fresh{H in
         lhs === List.cons(u,H) && rhs === List.empty &&
         delayed(sum_aux (H, rhs, ans, List.cons(u,temp)))
      }})
      ||
      // rhs -EA-> H;u, lhs -EA-> nil
      // ----------------------------
      // sum(lhs,rhs) -EA-> H;u
      (fresh{u in fresh{H in
         rhs === List.cons(u,H) && lhs === List.empty &&
         delayed(sum_aux (lhs, H, ans, List.cons(u,temp)))
      }})
      ||
      // If both numbers are not nil, we extract their least significant digit
      // each, get their digit_sum, add the main result to the accumulator and
      // sum the carry (if not 0) to the rest of lhs to call sum_aux recursively.
      //
      // lhs -EA-> n1;u1, rhs -EA-> n2;u2, sum(u1,u2) -EA-> r;res,
      // sum(n1,r) -EA-> inc, sum(inc,n2) -EA-> N
      // --------------------------------------------------------
      // sum(lhs,rhs) -EA-> N;res
      (freshn{v in
         let n1 = v["n1"]
         let n2 = v["n2"]
         let r = v["r"]
         let u1 = v["u1"]
         let u2 = v["u2"]
         let res = v["res"]
         let inc = v["inc"]
         let rinc = v["rinc"]
         let dig = v["dig"]
         let rn1 = v["rn1"]
         return (
            lhs === List.cons(u1,n1) && rhs === List.cons(u2,n2) && // extract digits
            digit_sum(List.cons(u1,List.empty),List.cons(u2,List.empty),res,r) && // get digit_sum
            (
               (r === toNumber(0) && rinc === n1) || // If the carry is 0, leave the rest of lhs as is
               (
                  r === toNumber(1) && reverse(n1,rn1) && // Else, add it to lhs
                  delayed(sum(rn1,r,inc)) && reverse(inc,rinc)
               )
            ) &&
            res === List.cons(dig,List.empty) && // Extract the digit of the digit_sum
            delayed(sum_aux(rinc,n2,ans,List.cons(dig,temp))) // Recursive call
         )
      })
}
// Sum evaluation function.
func sum (_ lhs: Term, _ rhs: Term, _ ans: Term) -> Goal {
   return
      // Checks that at least one of the numbers is not nil (the sum undefined
      // in this case)
      (
         isnumber(lhs) && isnumber(rhs) ||
         isnumber(lhs) && rhs === List.empty ||
         lhs === List.empty && isnumber(rhs)
      ) &&
      fresh{l in fresh{r in
         // Reverses the numbers to get the least significant digits first
         reverse(lhs, l) && reverse(rhs, r) &&
         // Calls the auxiliary function with a readied empty accumulator
         sum_aux(l, r, ans, List.empty)
      }}
}

// Auxiliary function to minus.
// temp holds the tested solution that gets incremented each time.
func minus_aux (_ lhs: Term, _ rhs: Term, _ ans: Term, _ temp: Term) -> Goal {
   return
      fresh{x in
         // The sum of rhs and temp is x
         sum(rhs,temp,x) &&
         (
            // If x is rhs, we have found the solution
            (x === lhs && ans === temp) ||
            (
               // Else, we increment temp and try again recursively
               neq(x,lhs) &&
               fresh{y in
                  sum(temp,toNumber(1),y) &&
                  delayed(minus_aux(lhs,rhs,ans,y))
               }
            )
         )
      }
}
// Subtraction evaluation function
func minus (_ lhs: Term, _ rhs: Term, _ ans: Term) -> Goal {
   return
      // We simply find ans such that temp+rhs==lhs.
      // Maybe because of a limitation of Swift or Logickit however the
      // evaluation of this can't end (probably because of the evaluation not
      // being lazy enough and the infinity of the numbers to test). To counter
      // that, we recursively increment a temporary value and check if it is the
      // solution. This "forces" the evaluation to go sequentially but
      // effectively works like the description below. (sorry, long explanation)
      //
      // loet(lhs,rhs), sum(n,rhs) -EA-> lhs
      // ---------------------------------------------------------
      // minus(lhs,rhs) -EA-> n
      loet(rhs,lhs) && minus_aux(lhs,rhs,ans,toNumber(0))
}

// Auxiliary function to prod.
// temp holds the intermediary sum as the product is computed.
// WARNING: This function is not well optimized. It is not recommended to use it
//          with big numbers (especially for rhs) ! ... except if you're patient.
func prod_aux (_ lhs: Term, _ rhs: Term, _ ans: Term, _ temp: Term) -> Goal {
   return
      // If rhs is 0, temp is the solution.
      //
      // rhs -EA-> 0
      // ---------------------
      // prod(lhs,rhs) -EA-> 0
      (rhs === toNumber(0) && ans === temp)
      ||
      // Else, we sum lhs to temp and decrement rhs to call prod_aux recursively
      //
      // minus(rhs,1) -EA-> y, prod(lhs,y) -EA-> s, sum(lhs,s) -EA-> x
      // ------------------------------------------------------------------
      // prod(lhs,rhs) -EA-> x
      (
         fresh{x in fresh{y in
            sum(temp,lhs,x) && minus(rhs,toNumber(1),y) &&
            delayed(prod_aux(lhs,y,ans,x))
         }}
      )
}
// Product evaluation function
func prod (_ lhs: Term, _ rhs: Term, _ ans: Term) -> Goal {
   return
      // We start at temp=0 and, rhs times, we add lhs to it
      prod_aux(lhs,rhs,ans,toNumber(0))
}

// Auxiliary function to div.
// temp holds the tested solution that gets incremented each time.
func div_aux(_ lhs: Term, _ rhs: Term, _ ans: Term, _ temp: Term) -> Goal {
   return
      fresh{x in
         // x is the product of rhs and temp
         prod(rhs,temp,x) &&
         (
            // If x is lhs, we have an exact solution
            (x === lhs && ans === temp) ||
            // If x is bigger than lhs, we have moved passed the exact solution
            // and round down to get the answer (without the remainder)
            (lt(lhs,x) && minus(temp,toNumber(1),ans)) ||
            (
               // Else, we haven't reached the solution yet and increment temp
               // to call div_aux recursively
               lt(x,lhs) &&
               fresh{y in
                  sum(temp,toNumber(1),y) &&
                  delayed(div_aux(lhs,rhs,ans,y))
               }
            )
         )
      }
}
// Integer division evaluation function
func div (_ lhs: Term, _ rhs: Term, _ ans: Term) -> Goal {
   return
      // Works with the same idea as the subtraction evaluation. We can either
      // have an natural number which is an exact solution, or round down to one.
      //
      // prod(rhs,n) -EA-> lhs
      // ---------------------
      // div(lhs,rhs) -EA-> n
      //
      // prod(rhs,n) -EA-> r, lt(r,lhs), prod(rhs,sum(n,1)) -EA-> r', lt(lhs,r')
      // -----------------------------------------------------------------------
      // div(lhs,rhs) -EA-> n
      div_aux(lhs,rhs,ans,toNumber(0))
}

// Arithmetic evaluation for at most a single operation
func evalArithmetic (input: Term, output: Term) -> Goal {
   // A number is evaluated to itself, while the operations are matched to their
   // respective evaluation with the same operands.
    return
      // ---------
      // n -EA-> n
      (isnumber(input) && output === input)
      ||
      fresh{l in fresh{r in
         // sum(l,r) -EA-> s
         // ----------------
         // add(l,r) -EA-> s
         (input === add(l,r) && sum(l,r,output))
         ||
         // minus(l,r) -EA-> s
         // ---------------------
         // subtract(l,r) -EA-> s
         (input === subtract(l,r) && minus(l,r,output))
         ||
         // prod(l,r) -EA-> s
         // ---------------------
         // multiply(l,r) -EA-> s
         (input === multiply(l,r) && prod(l,r,output))
         ||
         // div(l,r) -EA-> s
         // -------------------
         // divide(l,r) -EA-> s
         (input === divide(l,r) && div(l,r,output))
      }}
}

/********************************** Booleans **********************************/

// Boolean evaluation for at most a single operation
func evalBoolean (input: Term, output: Term) -> Goal {
   // The constants are evaluated as themselves. An operation is simply
   // evaluated according to its truth table (we consider that the operands are
   // already t or f).
   return
      // Constants
      //
      // ---------------
      // true -EB-> true
      (input === t && output === t)
      ||
      //
      // -----------------
      // false -EB-> false
      (input === f && output === f)
      ||
      // Not
      delayed(freshn{v in
        let b = v ["b"]
        return (
            input === not(b) &&
            // b -EB-> t
            // --------------
            // not(b) -EB-> f
            ((b === t && output === f) ||
            // b -EB-> f
            // --------------
            // not(b) -EB-> t
            (b === f && output === t))
        )
      })
      ||
      // And
      delayed(freshn{v in
        let l = v ["l"]
        let r = v ["r"]
        return
            (input === and(l, r)) &&
            (
               // l -EB-> t, r -EB-> t
               // --------------------
               // and(l,r) -EB-> t
               (l === t && r === t && output === t) ||
               // l -EB-> f
               // ----------------
               // and(l,r) -EB-> f
               (l === f && output === f) ||
               // r -EB-> f
               // ----------------
               // and(l,r) -EB-> f
               (r === f && output === f)
            )
      })
      ||
      // Or
      delayed(freshn{v in
        let l = v ["l"]
        let r = v ["r"]
        return
            (input === or(l, r)) &&
            (
               // l -EB-> f, r -EB-> f
               // --------------------
               // and(l,r) -EB-> f
               (l === f && r === f && output === f) ||
               // l -EB-> t
               // ----------------
               // and(l,r) -EB-> t
               (l === t && output === t) ||
               // r -EB-> t
               // ----------------
               // and(l,r) -EB-> t
               (r === t && output === t)
            )
      })
      ||
      // Implies
      delayed(freshn{v in
        let l = v ["l"]
        let r = v ["r"]
        return
            (input === implies(l, r)) &&
            (
               // l -EB-> t, r -EB-> f
               // --------------------
               // and(l,r) -EB-> f
               (l === t && r === f && output === f) ||
               // l -EB-> f
               // ----------------
               // and(l,r) -EB-> t
               (l === f && output === t) ||
               // l -EB-> t, r -EB-> t
               // --------------------
               // and(l,r) -EB-> t
               (l === t && r === t && output === t)
            )
      })
}

/******************************** Comparisons *********************************/
// Note: For practical reasons, the comparison evaluation functions never
// actually have a boolean in their substitutions, but instead simply allow 1
// substitution if true, and 0 otherwise.
// The boolean output value is assigned in evalComparison.

// Equality function
func eq (_ lhs: Term, _ rhs: Term) -> Goal {
   // Simply checks if a union is possible
   return
      // t -EA-> n, t' -EA-> n', n =={N} n'
      // ----------------------------------
      // eq(t,t') -R-> true
      (lhs === rhs)
}

// Checks inequality between digits
func digit_neq (_ lhs: Term, _ rhs: Term) -> Goal {
   // Straightforward comparison
   return
      // lhs -EA-> d, rhs -EA-> d', d !={N} d'
      // -------------------------------------
      // digit_neq(lhs,rhs) -R-> true
      //
      // 0
      (lhs === d0 && rhs === d1) ||
      (lhs === d0 && rhs === d2) ||
      (lhs === d0 && rhs === d3) ||
      (lhs === d0 && rhs === d4) ||
      (lhs === d0 && rhs === d5) ||
      (lhs === d0 && rhs === d6) ||
      (lhs === d0 && rhs === d7) ||
      (lhs === d0 && rhs === d8) ||
      (lhs === d0 && rhs === d9) ||
      // 1
      (lhs === d1 && rhs === d0) ||
      (lhs === d1 && rhs === d2) ||
      (lhs === d1 && rhs === d3) ||
      (lhs === d1 && rhs === d4) ||
      (lhs === d1 && rhs === d5) ||
      (lhs === d1 && rhs === d6) ||
      (lhs === d1 && rhs === d7) ||
      (lhs === d1 && rhs === d8) ||
      (lhs === d1 && rhs === d9) ||
      // 2
      (lhs === d2 && rhs === d0) ||
      (lhs === d2 && rhs === d1) ||
      (lhs === d2 && rhs === d3) ||
      (lhs === d2 && rhs === d4) ||
      (lhs === d2 && rhs === d5) ||
      (lhs === d2 && rhs === d6) ||
      (lhs === d2 && rhs === d7) ||
      (lhs === d2 && rhs === d8) ||
      (lhs === d2 && rhs === d9) ||
      // 3
      (lhs === d3 && rhs === d0) ||
      (lhs === d3 && rhs === d1) ||
      (lhs === d3 && rhs === d2) ||
      (lhs === d3 && rhs === d4) ||
      (lhs === d3 && rhs === d5) ||
      (lhs === d3 && rhs === d6) ||
      (lhs === d3 && rhs === d7) ||
      (lhs === d3 && rhs === d8) ||
      (lhs === d3 && rhs === d9) ||
      // 4
      (lhs === d4 && rhs === d0) ||
      (lhs === d4 && rhs === d1) ||
      (lhs === d4 && rhs === d2) ||
      (lhs === d4 && rhs === d3) ||
      (lhs === d4 && rhs === d5) ||
      (lhs === d4 && rhs === d6) ||
      (lhs === d4 && rhs === d7) ||
      (lhs === d4 && rhs === d8) ||
      (lhs === d4 && rhs === d9) ||
      // 5
      (lhs === d5 && rhs === d0) ||
      (lhs === d5 && rhs === d1) ||
      (lhs === d5 && rhs === d2) ||
      (lhs === d5 && rhs === d3) ||
      (lhs === d5 && rhs === d4) ||
      (lhs === d5 && rhs === d6) ||
      (lhs === d5 && rhs === d7) ||
      (lhs === d5 && rhs === d8) ||
      (lhs === d5 && rhs === d9) ||
      // 6
      (lhs === d6 && rhs === d0) ||
      (lhs === d6 && rhs === d1) ||
      (lhs === d6 && rhs === d2) ||
      (lhs === d6 && rhs === d3) ||
      (lhs === d6 && rhs === d4) ||
      (lhs === d6 && rhs === d5) ||
      (lhs === d6 && rhs === d7) ||
      (lhs === d6 && rhs === d8) ||
      (lhs === d6 && rhs === d9) ||
      // 7
      (lhs === d7 && rhs === d0) ||
      (lhs === d7 && rhs === d1) ||
      (lhs === d7 && rhs === d2) ||
      (lhs === d7 && rhs === d3) ||
      (lhs === d7 && rhs === d4) ||
      (lhs === d7 && rhs === d5) ||
      (lhs === d7 && rhs === d6) ||
      (lhs === d7 && rhs === d8) ||
      (lhs === d7 && rhs === d9) ||
      // 8
      (lhs === d8 && rhs === d0) ||
      (lhs === d8 && rhs === d1) ||
      (lhs === d8 && rhs === d2) ||
      (lhs === d8 && rhs === d3) ||
      (lhs === d8 && rhs === d4) ||
      (lhs === d8 && rhs === d5) ||
      (lhs === d8 && rhs === d6) ||
      (lhs === d8 && rhs === d7) ||
      (lhs === d8 && rhs === d9) ||
      // 9
      (lhs === d9 && rhs === d0) ||
      (lhs === d9 && rhs === d1) ||
      (lhs === d9 && rhs === d2) ||
      (lhs === d9 && rhs === d3) ||
      (lhs === d9 && rhs === d4) ||
      (lhs === d9 && rhs === d5) ||
      (lhs === d9 && rhs === d6) ||
      (lhs === d9 && rhs === d7) ||
      (lhs === d9 && rhs === d8)
}
// Inequality function
func neq (_ lhs: Term, _ rhs: Term) -> Goal {
   // This will allow to find a substitution if - either way:
   // * One of the to number ends before the other (they're of different legnths)
   // * They have a different digit at certain index
   // Otherwise, no substitution will be found
   return
      freshn{v in
         let l = v["l"]
         let L = v["L"]
         let r = v["r"]
         let R = v["R"]
         return
            // lhs -EA-> nil, rhs -EA-> r;R
            // ----------------------------
            // neq(lhs,rhs) -R-> true
            (lhs === List.empty && rhs === List.cons(r,R)) // Left ends first means true
            ||
            // lhs -EA-> l;L, rhs -EA-> nil
            // ----------------------------
            // neq(lhs,rhs) -R-> true
            (lhs === List.cons(l,L) && rhs === List.empty) // Right ends first means true
            ||
            // lhs -EA-> l;L, rhs -EA-> r;R, l !={N} r
            // ---------------------------------------
            // neq(lhs,rhs) -R-> true
            //
            // lhs -EA-> l;L, rhs -EA-> r;R, l =={N} r, neq(L,R) -EB-> b
            // ---------------------------------------------------------
            // neq(lhs,rhs) -R-> b
            (lhs === List.cons(l,L) && rhs === List.cons(r,R))
            &&
            (
               digit_neq(l,r) || // Different digits means true
               (eq(l,r) && delayed(neq(L,R))) // Otherwise check the rest of the digits
            )
      }
}

// Auxiliary function to lt AND loet
func lt_aux (_ lhs: Term, _ rhs: Term, _ count: Term) -> Goal {
   // We increment a counter until it reaches rhs (which means false), or lhs
   // (which means true).
   return
      // If the counter has reached lhs, lhs is inferior or equal to rhs
      //
      // eq(c,l) -R-> true
      // ------------------------
      // lt_aux(l,r,c) -R-> true
      eq(count,lhs)
      ||
      // If the counter has not yet reached either lhs or rhs, we increment it
      // to call lt_aux recursively.
      //
      // neq(c,l) -R-> true, neq(c,r) -R-> true,
      // sum(c,1) -EA-> x, lt_aux(l,r,x) -EA-> b
      // ---------------------------------------
      // lt_aux(l,r,c) -R-> b
      (
         neq(count,lhs) && neq(count,rhs) &&
         fresh{x in
            sum(count,toNumber(1),x) &&
            delayed(lt_aux(lhs,rhs,x))
         }
      )
}

// Strictly inferior check function
func lt (_ lhs: Term, _ rhs: Term) -> Goal {
   // We use lt_aux to check if lhs is inferior or equal to rhs, but also verify
   // that they are not equal.
   //
   // neq(l,r) -R-> true, lt_aux(l,r,0) -EA-> b
   // -----------------------------------------
   // lt(lhs,rhs) -R-> b
   //
   // neq(l,r) -R-> false
   // --------------------
   // lt(l,r) -R-> false
   return neq(lhs,rhs) && lt_aux(lhs, rhs, toNumber(0))
}

// inferior or equal check function
func loet (_ lhs: Term, _ rhs: Term) -> Goal {
   // We use lt_aux to check if lhs is inferior or equal to rhs.
   //
   // lt_aux(l,r,0) -EA-> b
   // ---------------------
   // loet(lhs,rhs) -R-> b
   return lt_aux(lhs, rhs, toNumber(0))
}

// Relation evaluation for at most a single operation
func evalComparison (input: Term, output: Term) -> Goal {
   // Evaluates the corresponding comparison, and sets output to true if it
   // yields a substitution and false if its negation does.
    return
      fresh{l in fresh{r in
         // ==
         (
            input === equal(l,r) &&
            (
               // eq(l,r) -R-> true
               // -----------------
               // equal(l,r) -R-> t
               (eq(l,r) && output === t) ||
               // neq(l,r) -R-> true
               // ------------------
               // equal(l,r) -R-> f
               (neq(l,r) && output === f)
            )
         )
         ||
         // !=
         (
            input === notequal(l,r) &&
            (
               // eq(l,r) -R-> true
               // --------------------
               // notequal(l,r) -R-> f
               (eq(l,r) && output === f) ||
               // neq(l,r) -R-> true
               // --------------------
               // notequal(l,r) -R-> t
               (neq(l,r) && output === t)
            )
         )
         ||
         // <
         (
            input === lessthan(l,r) &&
            (
               // lt(l,r) -R-> true
               // --------------------
               // lessthan(l,r) -R-> t
               (lt(l,r) && output === t) ||
               // loet(r,l) -R-> true
               // --------------------
               // lessthan(l,r) -R-> f
               (loet(r,l) && output === f)
            )
         )
         ||
         // <=
         (
            input === lessequal(l,r) &&
            (
               // loet(l,r) -R-> true
               // ---------------------
               // lessequal(l,r) -R-> t
               (loet(l,r) && output === t) ||
               // lt(r,l) -R-> true
               // ---------------------
               // lessequal(l,r) -R-> f
               (lt(r,l) && output === f)
            )
         )
         ||
         // >
         (
            input === greaterthan(l,r) &&
            (
               // lt(r,l) -R-> true
               // -----------------------
               // greaterthan(l,r) -R-> t
               (lt(r,l) && output === t) ||
               // loet(l,r) -R-> true
               // -----------------------
               // greaterthan(l,r) -R-> f
               (loet(l,r) && output === f)
            )
         )
         ||
         // >=
         (
            input === greaterequal(l,r) &&
            (
               // loet(r,l) -R-> true
               // ------------------------
               // greaterequal(l,r) -R-> t
               (loet(r,l) && output === t) ||
               // lt(l,r) -R-> true
               // ------------------------
               // greaterequal(l,r) -R-> f
               (lt(l,r) && output === f)
            )
         )
      }}
}

/***** Helper eval functions (because Swift couldn't handle long returns) *****/

// Evaluates an arithmetic operation after its operands
func arithmetic_aux (input: Term, output: Term) -> Goal {
   return
      // n -EA-> n
      // ---------
      // n -> n
      //
      // op in {add,subtract,multiply,divide}
      // l -> el, r -> er, op(el,er) -EA-> n
      // -----------------------------------
      // op(l,r) -> n
      fresh{l in fresh{r in fresh{ein in
         (
            (
               (isnumber(input) && ein === input)
               ||
               fresh{el in fresh{er in fresh{op in
                  input === Map(["op": op, "lhs": l, "rhs": r]) &&
                  delayed(eval(input: l, output: el)) &&
                  delayed(eval(input: r, output: er)) &&
                  (op === Value("+") || op === Value("-") ||
                  op === Value("*") || op === Value("/")) &&
                  ein === Map(["op": op, "lhs": el, "rhs": er])
               }}}
            ) &&
            evalArithmetic(input: ein, output: output)
         )
      }}}
}

// Evaluates a logic operation after its operands
func logic_aux (input: Term, output: Term) -> Goal {
   return
      // b -EB-> b
      // ---------
      // b -> b
      //
      // b -> eb, not(eb) -EB-> b'
      // -----------------------------------
      // not(b) -> b'
      //
      // op in {and,or,implies}
      // l -> el, r -> er, op(el,er) -EB-> b
      // -----------------------------------
      // op(l,r) -> b
      fresh{l in fresh{r in fresh{ein in
         (
            (
               ((input === t || input === f) && ein === input)
               ||
               fresh{el in fresh{op in
                  input === Map(["op": Value("¬"), "of": l]) &&
                  delayed(eval(input: l, output: el)) &&
                  ein === not(el)
               }}
               ||
               fresh{el in fresh{er in fresh{op in
                  input === Map(["op": op, "lhs": l, "rhs": r]) &&
                  delayed(eval(input: l, output: el)) &&
                  delayed(eval(input: r, output: er)) &&
                  (op === Value("∧") || op === Value("∨") ||
                  op === Value("=>")) &&
                  ein === Map(["op": op, "lhs": el, "rhs": er])
               }}}
            ) &&
            evalBoolean(input: ein, output: output)
         )
      }}}
}

// Evaluates a comparison operation after its operands
func relation_aux (input: Term, output: Term) -> Goal {
   return
      // op in {equal,notequal,lessthan,lessequal,greaterthan,greaterequal}
      // l -> el, r -> er, op(el,er) -R-> b
      // ----------------------------------
      // op(l,r) -> b
      fresh{l in fresh{r in fresh{ein in
         (
            fresh{el in fresh{er in fresh{op in
               input === Map(["op": op, "lhs": l, "rhs": r]) &&
               delayed(eval(input: l, output: el)) &&
               delayed(eval(input: r, output: er)) &&
               (op === Value("==") || op === Value("!=") ||
               op === Value("<") || op === Value("≤") ||
               op === Value(">") || op === Value("≥")) &&
               ein === Map(["op": op, "lhs": el, "rhs": er]) &&
               evalComparison(input: ein, output: output)
            }}}
         )
      }}}
}

// Main evaluation:

func eval (input: Term, output: Term) -> Goal {
   // This requires calls to auxiliary functions, because otherwise, the
   // compiler panics in front of the big mean return call.
    return
      // Arithmetic
      arithmetic_aux(input: input, output: output)
      ||
      // Logic
      logic_aux(input: input, output: output)
      ||
      // Relation
      relation_aux(input: input, output: output)
}
