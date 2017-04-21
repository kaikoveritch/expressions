import LogicKit

/* Information:
 * Digits is self-explanatory
 * EA is the set of all arithmetic expressions
 * EB is the set of all boolean expressions
 * R is the set of all relations
 */

func reverse_aux (_ L: Term, _ R: Term, _ G: Term) -> Goal {
   return
      (L === List.empty && R === G)
      ||
      (
         fresh{el in fresh{H in
            L === List.cons(el, H)
            &&
            delayed(reverse_aux (H, R, List.cons(el,G)))
         }}
      )
}

func reverse (_ L: Term, _ R: Term) -> Goal {
   return
      reverse_aux (L, R, List.empty)
}

// Numbers:

// n in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
// -----------------------------------
// n in Digits
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

// d in Digits
// -------------------
// cons(d,empty) in EA
//
// d in Digits, n in EA
// --------------------
// cons(d,n) in EA
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

// Evaluation:

/********************************* Arithmetic *********************************/

func digit_sum (_ lhs: Term, _ rhs: Term, _ ans: Term, _ carry: Term) -> Goal {
   return
      /********************************* 0+x **********************************/
      // ----------------------
      // sum(d0,d0) -EA-> 0;0
      (lhs === toNumber(0) && rhs === toNumber(0) && ans === toNumber(0) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d0,d1) -EA-> 0;1
      (lhs === toNumber(0) && rhs === toNumber(1) && ans === toNumber(1) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d0,d2) -EA-> 0;2
      (lhs === toNumber(0) && rhs === toNumber(2) && ans === toNumber(2) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d0,d3) -EA-> 0;3
      (lhs === toNumber(0) && rhs === toNumber(3) && ans === toNumber(3) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d0,d4) -EA-> 0;4
      (lhs === toNumber(0) && rhs === toNumber(4) && ans === toNumber(4) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d0,d5) -EA-> 0;5
      (lhs === toNumber(0) && rhs === toNumber(5) && ans === toNumber(5) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d0,d6) -EA-> 0;6
      (lhs === toNumber(0) && rhs === toNumber(6) && ans === toNumber(6) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d0,d7) -EA-> 0;7
      (lhs === toNumber(0) && rhs === toNumber(7) && ans === toNumber(7) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d0,d8) -EA-> 0;8
      (lhs === toNumber(0) && rhs === toNumber(8) && ans === toNumber(8) && carry === toNumber(0))
      ||
      // ----------------------
      // sum(d0,d9) -EA-> 0;9
      (lhs === toNumber(0) && rhs === toNumber(9) && ans === toNumber(9) && carry === toNumber(0))
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

func sum_aux(_ lhs: Term, _ rhs: Term, _ ans: Term, _ temp: Term) -> Goal {
   return
      // lhs -EA-> nil, rhs -EA-> nil
      // ----------------------------
      // sum(lhs,rhs) -EA-> nil
      (lhs === List.empty && rhs === List.empty && ans === temp)
      ||
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
      // lhs -EA-> n1;u1, rhs -EA-> n2;u2, sum(u1,u2) -EA-> r;res
      // --------------------------------------------------------
      // sum(lhs,rhs) -EA-> sum(sum(n1,r),n2);res
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
            lhs === List.cons(u1,n1) && rhs === List.cons(u2,n2) &&
            digit_sum(List.cons(u1,List.empty),List.cons(u2,List.empty),res,r) &&
            (
               (r === toNumber(0) && rinc === n1) ||
               (
                  r === toNumber(1) && reverse(n1,rn1) &&
                  delayed(sum(rn1,r,inc)) && reverse(inc,rinc)
               )
            ) &&
            res === List.cons(dig,List.empty) &&
            delayed(sum_aux(rinc,n2,ans,List.cons(dig,temp)))
         )
      })
}
func sum(_ lhs: Term, _ rhs: Term, _ ans: Term) -> Goal {
   return
      fresh{l in fresh{r in
         reverse(lhs, l) && reverse(rhs, r) &&
         sum_aux(l, r, ans, List.empty)
      }}
}

func minus(_ lhs: Term, _ rhs: Term, _ ans: Term) -> Goal {
   assert(false)
}

func evalArithmetic (input: Term, output: Term) -> Goal {
    assert (false)
}

/********************************** Booleans **********************************/

func evalBoolean (input: Term, output: Term) -> Goal {
   return
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
      // b -EB-> eb
      // ------------------------
      // not(b) -EB-> not{Bool}eb
      delayed(freshn{v in
        let b = v ["b"]
        let eb = v ["eb"]
        return (
            input === not(b) && evalBoolean(input: b, output: eb) &&
            ((eb === t && output === f) ||
            (eb === f && output === t))
        )
      })
      ||
      // l -EB-> el, r -EB-> er
      // ----------------------------
      // and(l,r) -EB-> l and{Bool} r
      delayed(freshn{v in
        let l = v ["l"]
        let r = v ["r"]
        let el = v ["el"]
        let er = v ["er"]
        return
            (input === and(l, r)) &&
            evalBoolean(input: l, output: el) &&
            evalBoolean(input: r, output: er) &&
            (
               (el === t && er === t && output === t) ||
               (el === f && output === f) ||
               (er === f && output === f)
            )
      })
      ||
      // l -EB-> el, r -EB-> er
      // --------------------------
      // or(l,r) -EB-> l or{Bool} r
      delayed(freshn{v in
        let l = v ["l"]
        let r = v ["r"]
        let el = v ["el"]
        let er = v ["er"]
        return
            (input === or(l, r)) &&
            evalBoolean(input: l, output: el) &&
            evalBoolean(input: r, output: er) &&
            (
               (el === f && er === f && output === f) ||
               (el === t && output === t) ||
               (er === t && output === t)
            )
      })
      ||
      // l -EB-> el, r -EB-> er
      // -------------------------------
      // implies(l,r) -EB-> l =>{Bool} r
      delayed(freshn{v in
        let l = v ["l"]
        let r = v ["r"]
        let el = v ["el"]
        let er = v ["er"]
        return
            (input === implies(l, r)) &&
            evalBoolean(input: l, output: el) &&
            evalBoolean(input: r, output: er) &&
            (
               (el === t && er === f && output === f) ||
               (el === f && output === t) ||
               (el === t && er === t && output === t)
            )
      })
}

/******************************** Comparisons *********************************/

func eq (_ lhs: Term, _ rhs: Term) -> Goal {
   return
      // t -EA-> n, t' -EA-> n', n =={N} n'
      // ----------------------------------
      // eq(t,t') -R-> true
      (lhs === rhs)
}

func digit_neq (_ lhs: Term, _ rhs: Term) -> Goal {
   return
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
func neq (_ lhs: Term, _ rhs: Term) -> Goal {
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
            (lhs === List.empty && rhs === List.cons(r,R))
            ||
            // lhs -EA-> l;L, rhs -EA-> nil
            // ----------------------------
            // neq(lhs,rhs) -R-> true
            (lhs === List.cons(l,L) && rhs === List.empty)
            ||
            // lhs -EA-> l;L, rhs -EA-> r;R, l !={N} r
            // ---------------------------------------
            // neq(lhs,rhs) -R-> true
            //
            // lhs -EA-> l;L, rhs -EA-> r;R, l =={N} r
            // ---------------------------------------
            // neq(lhs,rhs) -R-> neq(L,R)
            (lhs === List.cons(l,L) && rhs === List.cons(r,R))
            &&
            (
               digit_neq(l,r) ||
               (eq(l,r) && delayed(neq(L,R)))
            )
      }
}

func lt_aux (_ lhs: Term, _ rhs: Term, _ count: Term) -> Goal {
   return
      // eq(c,t) -R-> true
      // ------------------------
      // lt_aux(t,t',c) -R-> true
      eq(count,lhs)
      ||
      // neq(c,t) -R-> true, neq(c,t') -R-> true
      // -----------------------------------------
      // lt_aux(t,t',c) -R-> lt_aux(t,t',sum(c,1))
      (
         neq(count,lhs) && neq(count,rhs) &&
         fresh{x in
            sum(count,toNumber(1),x) &&
            delayed(lt_aux(lhs,rhs,x))
         }
      )
}
func lt (_ lhs: Term, _ rhs: Term) -> Goal {
   // neq(t,t') -R-> true
   // ----------------------------
   // lt(t,t') -R-> lt_aux(t,t',0)
   //
   // neq(t,t') -R-> false
   // --------------------
   // lt(t,t') -R-> false
   return neq(lhs,rhs) && lt_aux(lhs, rhs, toNumber(0))
}

func loet (_ lhs: Term, _ rhs: Term) -> Goal {
   return lt_aux(lhs, rhs, toNumber(0))
}

func evalComparison (input: Term, output: Term) -> Goal {
    return
      fresh{l in fresh{r in
         // ==
         (
            input === equal(l,r) &&
            (
               (eq(l,r) && output === t) ||
               (neq(l,r) && output === f)
            )
         )
         ||
         // !=
         (
            input === notequal(l,r) &&
            (
               (eq(l,r) && output === f) ||
               (neq(l,r) && output === t)
            )
         )
         ||
         // <
         (
            input === lessthan(l,r) &&
            (
               (lt(l,r) && output === t) ||
               (loet(r,l) && output === f)
            )
         )
         ||
         // <=
         (
            input === lessequal(l,r) &&
            (
               (loet(l,r) && output === t) ||
               (lt(r,l) && output === f)
            )
         )
         ||
         // >
         (
            input === greaterthan(l,r) &&
            (
               (lt(r,l) && output === t) ||
               (loet(l,r) && output === f)
            )
         )
         ||
         // >=
         (
            input === greaterequal(l,r) &&
            (
               (loet(r,l) && output === t) ||
               (lt(l,r) && output === f)
            )
         )
      }}
}

// Main evaluation:

func eval (input: Term, output: Term) -> Goal {
    assert (false)
}
