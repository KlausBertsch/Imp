package main

import "fmt"
import "strconv"

// Simple imperative language

/*
vars       Variable names, start with lower-case letter

prog      ::= block
block     ::= "{" statement "}"
statement ::=  statement ";" statement           -- Command sequence
            |  vars ":=" exp                     -- Variable declaration
            |  vars "=" exp                      -- Variable assignment
            |  "while" exp block                 -- While
            |  "if" exp block "else" block       -- If-then-else
            |  "print" exp                       -- Print

exp ::= 0 | 1 | -1 | ...     -- Integers
     | "true" | "false"      -- Booleans
     | exp "+" exp           -- Addition
     | exp "*" exp           -- Multiplication
     | exp "||" exp          -- Disjunction
     | exp "&&" exp          -- Conjunction
     | "!" exp               -- Negation
     | exp "==" exp          -- Equality test
     | exp "<" exp           -- Lesser test
     | "(" exp ")"           -- Grouping of expressions
     | vars                  -- Variables
*/

// Values

type Kind int

const (
    ValueInt  Kind = 0
    ValueBool Kind = 1
    Undefined Kind = 2
)

type Val struct {
    flag Kind
    valI int
    valB bool
}

func mkInt(x int) Val {
    return Val{flag: ValueInt, valI: x}
}
func mkBool(x bool) Val {
    return Val{flag: ValueBool, valB: x}
}
func mkUndefined() Val {
    return Val{flag: Undefined}
}

func showVal(v Val) string {
    var s string
    switch {
    case v.flag == ValueInt:
        s = Num(v.valI).pretty()
    case v.flag == ValueBool:
        s = Bool(v.valB).pretty()
    case v.flag == Undefined:
        s = "Undefined"
    }
    return s
}

// Types

type Type int

const (
    TyIllTyped Type = 0
    TyInt      Type = 1
    TyBool     Type = 2
)

func showType(t Type) string {
    var s string
    switch {
    case t == TyInt:
        s = "Int"
    case t == TyBool:
        s = "Bool"
    case t == TyIllTyped:
        s = "Illtyped"
    }
    return s
}

// Value State is a mapping from variable names to values
type ValState map[string]Val

// Value State is a mapping from variable names to types
type TyState map[string]Type

// Interface

type Exp interface {
    pretty() string
    eval(s ValState) Val
    infer(t TyState) Type
}

type Stmt interface {
    pretty() string
    eval(s ValState)
    check(t TyState) bool
}

// Statement cases (incomplete)

type Seq [2]Stmt
type Decl struct {
    lhs string
    rhs Exp
}
type IfThenElse struct {
    cond     Exp
    thenStmt Stmt
    elseStmt Stmt
}

type Assign struct {
    lhs string
    rhs Exp
}

type While struct {
    cond Exp
    whileStmt Stmt
}

type Print struct {
    toPrint Exp
}



// Expression cases (incomplete)

type Bool bool
type Num int
type Mult [2]Exp
type Plus [2]Exp
type And [2]Exp
type Or [2]Exp
type Neg [1]Exp
type Equ [2]Exp
type Less [2]Exp
type Group [1]Exp
type Var string

/////////////////////////
// Stmt instances

// pretty print

func (stmt Seq) pretty() string {
    return stmt[0].pretty() + " ; " + stmt[1].pretty()
}

func (decl Decl) pretty() string {
    return decl.lhs + " := " + decl.rhs.pretty()
}

func (ite IfThenElse) pretty() string {
    return "if " + ite.cond.pretty() + " { " + ite.thenStmt.pretty() + " } else { " + ite.elseStmt.pretty() +" }"
}

func (printer Print) pretty() string {
    return "print " + printer.toPrint.pretty()
}

func (assign Assign) pretty() string {
    return assign.lhs + " = " + assign.rhs.pretty()
}

func (while While) pretty() string {
    return "while " + while.cond.pretty() + " { " + while.whileStmt.pretty() + " }"
}

// eval

func (stmt Seq) eval(s ValState) {
    stmt[0].eval(s)
    stmt[1].eval(s)
}

func (ite IfThenElse) eval(s ValState) {
    v := ite.cond.eval(s)
    if v.flag == ValueBool {
        switch {
        case v.valB:
            ite.thenStmt.eval(s)
        case !v.valB:
            ite.elseStmt.eval(s)
        }

    } else {
        fmt.Printf("if-then-else eval fail")
    }

}

func (while While) eval(s ValState) {
    v := while.cond.eval(s)
    if v.flag == ValueBool {
        for v.valB {
            while.whileStmt.eval(s)
            v = while.cond.eval(s)
            if v.flag != ValueBool {
                fmt.Printf("while eval fail")
            }
        }

    } else {
        fmt.Printf("while eval fail")
    }
}

func (printer Print) eval(s ValState) {
    x := printer.toPrint.eval(s)
    fmt.Printf("\n printer: %s", showVal(x))
}


// Maps are represented via points.
// Hence, maps are passed by "reference" and the update is visible for the caller as well.
func (decl Decl) eval(s ValState) {
    v := decl.rhs.eval(s)
    x := (string)(decl.lhs)
    s[x] = v
}

func (assign Assign) eval(s ValState) {
    v := assign.rhs.eval(s)
    x := (string)(assign.lhs)
    s[x] = v
}

// type check

func (stmt Seq) check(t TyState) bool {
    if !stmt[0].check(t) {
        return false
    }
    return stmt[1].check(t)
}

func (decl Decl) check(t TyState) bool {
    ty := decl.rhs.infer(t)
    if ty == TyIllTyped {
        return false
    }

    x := (string)(decl.lhs)
    t[x] = ty
    return true
}

func (a Assign) check(t TyState) bool {
        x := (string)(a.lhs)
        return t[x] == a.rhs.infer(t)
}

func (ite IfThenElse) check(t TyState) bool {
    ty := ite.cond.infer(t)
    if ty == TyIllTyped {
        return false
    }
    if !ite.thenStmt.check(t) {
        return false
    }
    return ite.elseStmt.check(t)
}

func (while While) check(t TyState) bool {
    ty := while.cond.infer(t)
    if ty == TyIllTyped {
        return false
    }
    return while.whileStmt.check(t)
}

func (printer Print) check(t TyState) bool {
    ty := printer.toPrint.infer(t)
    return ty != TyIllTyped
}


/////////////////////////
// Exp instances

// pretty print

func (x Var) pretty() string {
    return (string)(x)
}

func (x Bool) pretty() string {
    if x {
        return "true"
    } else {
        return "false"
    }

}

func (x Num) pretty() string {
    return strconv.Itoa(int(x))
}

func (e Mult) pretty() string {

    var x string
    x = "("
    x += e[0].pretty()
    x += "*"
    x += e[1].pretty()
    x += ")"

    return x
}

func (e Plus) pretty() string {

    var x string
    x = "("
    x += e[0].pretty()
    x += "+"
    x += e[1].pretty()
    x += ")"

    return x
}

func (e And) pretty() string {

    var x string
    x = "("
    x += e[0].pretty()
    x += "&&"
    x += e[1].pretty()
    x += ")"

    return x
}

func (e Or) pretty() string {

    var x string
    x = "("
    x += e[0].pretty()
    x += "||"
    x += e[1].pretty()
    x += ")"

    return x
}

func (e Neg) pretty() string {
    var x string
    x = "!"
    x += e[0].pretty()
    return x
}

func (e Equ) pretty() string {

    var x string
    x = "("
    x += e[0].pretty()
    x += "=="
    x += e[1].pretty()
    x += ")"

    return x
}

func (e Less) pretty() string {

    var x string
    x = "("
    x += e[0].pretty()
    x += "<"
    x += e[1].pretty()
    x += ")"

    return x
}

func (e Group) pretty() string {
        var x string
    x = "("
    x += e[0].pretty()
    x += ")"

    return x
}

// Evaluator

func (x Bool) eval(s ValState) Val {
    return mkBool((bool)(x))
}

func (x Num) eval(s ValState) Val {
    return mkInt((int)(x))
}

func (e Mult) eval(s ValState) Val {
    n1 := e[0].eval(s)
    n2 := e[1].eval(s)
    if n1.flag == ValueInt && n2.flag == ValueInt {
        return mkInt(n1.valI * n2.valI)
    }
    return mkUndefined()
}

func (e Plus) eval(s ValState) Val {
    n1 := e[0].eval(s)
    n2 := e[1].eval(s)
    if n1.flag == ValueInt && n2.flag == ValueInt {
        return mkInt(n1.valI + n2.valI)
    }
    return mkUndefined()
}

func (e And) eval(s ValState) Val {
    b1 := e[0].eval(s)
    b2 := e[1].eval(s)
    switch {
    case b1.flag == ValueBool && b1.valB == false:
        return mkBool(false)
    case b1.flag == ValueBool && b2.flag == ValueBool:
        return mkBool(b1.valB && b2.valB)
    }
    return mkUndefined()
}

func (e Or) eval(s ValState) Val {
    b1 := e[0].eval(s)
    b2 := e[1].eval(s)
    switch {
    case b1.flag == ValueBool && b1.valB == true:
        return mkBool(true)
    case b1.flag == ValueBool && b2.flag == ValueBool:
        return mkBool(b1.valB || b2.valB)
    }
    return mkUndefined()
}

func (e Neg) eval(s ValState) Val {
    b := e[0].eval(s)
    if(b.flag == ValueBool){
        return mkBool(!b.valB)
    }
    return mkUndefined()
}

func (e Equ) eval(s ValState) Val {
    b1 := e[0].eval(s)
    b2 := e[1].eval(s)
    switch {
    case b1.flag == ValueBool && b1.flag == ValueBool:
        return mkBool(b1.valB == b2.valB)
    case b1.flag == ValueInt && b2.flag == ValueInt:
        return mkBool(b1.valI == b2.valI)
    }
    return mkUndefined()
}

func (e Less) eval(s ValState) Val {
    b1 := e[0].eval(s)
    b2 := e[1].eval(s)
    if(b1.flag == ValueInt && b2.flag == ValueInt){
        return mkBool(b1.valI < b2.valI)
    }
    return mkUndefined()
}

func (e Group) eval(s ValState) Val {
    b := e[0].eval(s)
    switch{
    case b.flag == ValueBool:
        return mkBool(b.valB)
    case b.flag == ValueInt:
        return mkInt(b.valI)
    }
    return mkUndefined()
}

func(e Var) eval (s ValState) Val {
    y := (string)(e)
    b := s[y]
    switch{
    case b.flag == ValueBool:
        return mkBool(b.valB)
    case b.flag == ValueInt:
        return mkInt(b.valI)
    }
    return mkUndefined()
}
// Type inferencer/checker

func (x Var) infer(t TyState) Type {
    y := (string)(x)
    ty, ok := t[y]
    if ok {
        return ty
    } else {
        return TyIllTyped // variable does not exist yields illtyped
    }

}

func (x Bool) infer(t TyState) Type {
    return TyBool
}

func (x Num) infer(t TyState) Type {
    return TyInt
}

func (e Mult) infer(t TyState) Type {
    t1 := e[0].infer(t)
    t2 := e[1].infer(t)
    if t1 == TyInt && t2 == TyInt {
        return TyInt
    }
    return TyIllTyped
}

func (e Plus) infer(t TyState) Type {
    t1 := e[0].infer(t)
    t2 := e[1].infer(t)
    if t1 == TyInt && t2 == TyInt {
        return TyInt
    }
    return TyIllTyped
}

func (e And) infer(t TyState) Type {
    t1 := e[0].infer(t)
    t2 := e[1].infer(t)
    if t1 == TyBool && t2 == TyBool {
        return TyBool
    }
    return TyIllTyped
}

func (e Or) infer(t TyState) Type {
    t1 := e[0].infer(t)
    t2 := e[1].infer(t)
    if t1 == TyBool && t2 == TyBool {
        return TyBool
    }
    return TyIllTyped
}

func (e Neg) infer(t TyState) Type {
    t1 := e[0].infer(t)
    if t1 == TyBool {
        return TyBool
    }
    return TyIllTyped
}

func (e Equ) infer(t TyState) Type {
    t1 := e[0].infer(t)
    t2 := e[1].infer(t)
    if t1 == TyBool && t2 == TyBool {
        return TyBool
    }
    if t1 == TyInt && t2 == TyInt {
        return TyInt
    }
    return TyIllTyped
}

func (e Less) infer(t TyState) Type {
    t1 := e[0].infer(t)
    t2 := e[1].infer(t)
    if t1 == TyInt && t2 == TyInt {
        return TyInt
    }
    return TyIllTyped
}

func (e Group) infer(t TyState) Type {
    t1 := e[0].infer(t)
    if t1 == TyInt {
        return TyInt
    }
    if t1 == TyBool {
        return TyBool
    }
    return TyIllTyped
}
// Helper functions to build ASTs by hand

func number(x int) Exp {
    return Num(x)
}

func boolean(x bool) Exp {
    return Bool(x)
}

func plus(x, y Exp) Exp {
    return (Plus)([2]Exp{x, y})

    // The type Plus is defined as the two element array consisting of Exp elements.
    // Plus and [2]Exp are isomorphic but different types.
    // We first build the AST value [2]Exp{x,y}.
    // Then cast this value (of type [2]Exp) into a value of type Plus.

}

func mult(x, y Exp) Exp {
    return (Mult)([2]Exp{x, y})
}

func and(x, y Exp) Exp {
    return (And)([2]Exp{x, y})
}

func or(x, y Exp) Exp {
    return (Or)([2]Exp{x, y})
}

func equals(x, y Exp) Exp {
    return (Equ)([2]Exp{x, y})
}

func neg(x Exp) Exp {
    return (Neg)([1]Exp{x})
}

func less(x, y Exp) Exp {
    return (Less)([2]Exp{x, y})
}

func group(x Exp) Exp {
    return (Group)([1]Exp{x})
}

func variable(x string) Exp {
    return (Var)(x)
}

func ite (x Exp, y,z Stmt) Stmt {
    var ite IfThenElse
    ite.cond = x
    ite.thenStmt = y
    ite.elseStmt = z
    return ite
}

func while (x Exp, y Stmt) Stmt {
    var while While
    while.cond = x
    while.whileStmt = y
    return while
}

func printer (x Exp) Stmt {
    var printer Print
    printer.toPrint = x
    return printer
}

func assign (x string, y Exp) Stmt {
    var assign Assign
    assign.lhs = x
    assign.rhs = y
    return assign
}

func decl (x string, y Exp) Stmt {
    var decl Decl
    decl.lhs = x
    decl.rhs = y
    return decl
}

func seq (x,y Stmt) Stmt {
    var seq Seq
    seq[0] = x
    seq[1] = y
    return seq
}
    
// Examples

func run(e Exp) {
    s := make(map[string]Val)
    t := make(map[string]Type)
    fmt.Printf("\n ******* ")
    fmt.Printf("\n %s", e.pretty())
    fmt.Printf("\n %s", showVal(e.eval(s)))
    fmt.Printf("\n %s", showType(e.infer(t)))
}

func runSt(st Stmt) {
    s := make(map[string]Val)
    t := make(map[string]Type)
    fmt.Printf("\n ******* ")
    fmt.Printf("\n %s", st.pretty())
    st.eval(s)
    fmt.Printf("\n check: %t", st.check(t))
}

func ex1() {
    ast := plus(mult(number(1), number(2)), number(0))

    run(ast)
}

func ex2() {
    ast := equals(boolean(true), neg(boolean(false)))
    run(ast)
}

func ex3() {
    ast := or(boolean(false), number(0))
    run(ast)
}

func st1() {
    ast := seq(decl("x",number(1)),decl("x", less(variable("x"),number(2))))
    runSt(ast)
}

func st2() {
    ast := seq(decl("x",number(3)),printer(variable("x")))
    runSt(ast)
}

func st3() {
    ast := seq(decl("x",boolean(false)),seq(while(variable("x"),decl("x",number(1))),seq(decl("x",boolean(true)),printer(variable("x")))))
    runSt(ast)
}

func st4() {
    ast := seq(decl("x",number(5)),seq(while(less(variable("x"),number(10)),assign("x",plus(variable("x"),number(1)))),printer(variable("x"))))
    runSt(ast)
}

func st5() {
    ast := seq(decl("x",boolean(true)),seq(ite(variable("x"),assign("x",boolean(false)),assign("x",boolean(true))),printer(variable("x"))))
    runSt(ast)
}
func st6() {
    ast := seq(decl("x",boolean(false)),seq(ite(variable("x"),assign("x",boolean(false)),assign("x",boolean(true))),printer(variable("x"))))
    runSt(ast)
}

func main() {

    fmt.Printf("\n")

    ex1()
    ex2()
    ex3()
    st1()
    st2()
    st3()
    st4()
    st5()
    st6()
}
