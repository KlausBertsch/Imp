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

//key struct to identify Vals in a hierarchical manner and to allow local variables with same names
type key struct { //as higher level ones
    name string
    level int
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

type ValState map[key] Val
// Value State is a mapping from variable names to types
type TyState map[key]Type

// Interface

type Exp interface {
    pretty() string
    eval(s ValState,level int) Val
    infer(t TyState,level int) Type
}

type Stmt interface {
    pretty() string
    eval(s ValState,level int)
    check(t TyState,level int) bool
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
//spaces added for better appearance of print
func (ite IfThenElse) pretty() string {
    return "if " + ite.cond.pretty() + " { " + ite.thenStmt.pretty() + " } else { " + ite.elseStmt.pretty() +" }"
}

func (printer Print) pretty() string {
    return "print " + printer.toPrint.pretty()
}

func (assign Assign) pretty() string {
    return assign.lhs + " = " + assign.rhs.pretty()
}

//spaces added for better appearance of print
func (while While) pretty() string {
    return "while " + while.cond.pretty() + " { " + while.whileStmt.pretty() + " }"
}

// eval

func (stmt Seq) eval(s ValState,level int) {
    stmt[0].eval(s,level)//evaluate both statements
    stmt[1].eval(s,level)
}

func (ite IfThenElse) eval(s ValState,level int) {
    v := ite.cond.eval(s,level)
    if v.flag == ValueBool {
        switch {
        case v.valB:
            ite.thenStmt.eval(s,level+1)//add a level to the  Val map, so local variables can be added
        case !v.valB:
            ite.elseStmt.eval(s,level+1)//add a level to the  Val map, so local variables can be added
        }
        for k, _ := range s {// delete all variables added in the If-Then-Else Statement
            if k.level >= level+1 {
                delete(s,k)
            }
        }

    } else {
        fmt.Printf("if-then-else eval fail")
    }

}

func (while While) eval(s ValState,level int) {
    v := while.cond.eval(s,level)
    if v.flag == ValueBool {
        for v.valB {
            while.whileStmt.eval(s,level+1) //add a level to the  Val map, so local variables can be added
            v = while.cond.eval(s,level) //evaluation of the condition can only happen on the initial one
            if v.flag != ValueBool {
                fmt.Printf("while eval fail")
            }
        }
        for k, _ := range s { // delete all variables added in the While loop
            if k.level >= level+1 {
                delete(s,k)
            }
        }
    } else {
        fmt.Printf("while eval fail")
    }
}

func (printer Print) eval(s ValState,level int) {
    x := printer.toPrint.eval(s,level)
    fmt.Printf("\n printer: %s", showVal(x))//Expression is also printed, after evaluation
}

// Maps are represented via points.
// Hence, maps are passed by "reference" and the update is visible for the caller as well.
func (decl Decl) eval(s ValState,level int) {
    v := decl.rhs.eval(s,level)
    x := (string)(decl.lhs)
    s[key{x,level}] = v //add new variable on given level to ValState
}

func (assign Assign) eval(s ValState,level int) {
    v := assign.rhs.eval(s,level)
    x := (string)(assign.lhs)
    for i := level; i >= 0; i-- {//check for the variable on all higher levels, if there are any 
    k := key{x,i}
    if _, ok := s[k]; ok {//assign variable on highest level, a variable with that name exists
        s[k] = v
    }
    }
}

// type check

func (stmt Seq) check(t TyState,level int) bool {
    if !stmt[0].check(t,level) {//return false, since first statement is alrady not correctly typed
        return false
    }
    return stmt[1].check(t,level)//if first one was correctly typed, return the evaluation for the second statement
}

func (decl Decl) check(t TyState,level int) bool {
    ty := decl.rhs.infer(t,level)
    if ty == TyIllTyped { //Expression not correctly typed
        return false
    }
    x := (string)(decl.lhs)
    t[key{x,level}] = ty //set type on given level
    return true
}

func (a Assign) check(t TyState,level int) bool {
        x := (string)(a.lhs)
        for i := level; i >= 0; i-- {//check for the variable on all higher levels, if there are any 
            if val, ok := t[key{x,i}]; ok { //check whether variable exists
                return val == a.rhs.infer(t,level)  //if variable exists return whether given expression is
            }                                       //of correct type for the variable
        }
        return false // no variable with given name was found, return false
        
}

func (ite IfThenElse) check(t TyState,level int) bool {
    ret := false
    ty := ite.cond.infer(t,level)
    if ty == TyIllTyped {
        return false //Expression not correctly typed, statements do not have to be checked
    }
    if !ite.thenStmt.check(t,level+1) {//add a level for local variables in If-Then-Else Statement
        ret = false
    }
    ret = ite.elseStmt.check(t,level+1)//add a level for local variables in If-Then-Else Statement
    for k, _ := range t { // delete all types of variables added in the If-Then-Else Statement
        if k.level >= level+1 {
            delete(t,k)
        }
    }
    return ret
}

func (while While) check(t TyState,level int) bool {
    ret := false
    ty := while.cond.infer(t,level)
    if ty == TyIllTyped {
        return false//Expression not correctly typed, statements do not have to be checked
    }
    ret = while.whileStmt.check(t,level) //add a level for local variables in While Loop
    for k, _ := range t { // delete all types of variables added in the While loop
        if k.level >= level+1 {
            delete(t,k)
        }
    }
    return ret
}

func (printer Print) check(t TyState,level int) bool {
    ty := printer.toPrint.infer(t,level)
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

// Evaluator

func (x Bool) eval(s ValState,level int) Val {
    return mkBool((bool)(x))
}

func (x Num) eval(s ValState,level int) Val {
    return mkInt((int)(x))
}

func (e Mult) eval(s ValState,level int) Val {
    n1 := e[0].eval(s,level)
    n2 := e[1].eval(s,level)
    if n1.flag == ValueInt && n2.flag == ValueInt {
        return mkInt(n1.valI * n2.valI)
    }
    return mkUndefined()//wrong type was given in either Expression
}

func (e Plus) eval(s ValState,level int) Val {
    n1 := e[0].eval(s,level)
    n2 := e[1].eval(s,level)
    if n1.flag == ValueInt && n2.flag == ValueInt {
        return mkInt(n1.valI + n2.valI)
    }
    return mkUndefined()//wrong type was given in either Expression
}

func (e And) eval(s ValState,level int) Val {
    b1 := e[0].eval(s,level)
    b2 := e[1].eval(s,level)
    switch {
    case b1.flag == ValueBool && b1.valB == false:
        return mkBool(false) //first Expression is boolean and false, no more evaluation necessary
    case b1.flag == ValueBool && b2.flag == ValueBool:
        return mkBool(b1.valB && b2.valB) //both Expressions are boolean, return Evaluation
    }
    return mkUndefined() //wrong type was given in either Expression
}

func (e Or) eval(s ValState,level int) Val {
    b1 := e[0].eval(s,level)
    b2 := e[1].eval(s,level)
    switch {
    case b1.flag == ValueBool && b1.valB == true:
        return mkBool(true) //first Expression is boolean and true, no more evaluation necessary
    case b1.flag == ValueBool && b2.flag == ValueBool:
        return mkBool(b1.valB || b2.valB) //both Expressions are boolean, return Evaluation
    }
    return mkUndefined()//wrong type was given in either Expression
}

func (e Neg) eval(s ValState,level int) Val {
    b := e[0].eval(s,level)
    if(b.flag == ValueBool){ //only negate if val is of type boolean
        return mkBool(!b.valB)
    }
    return mkUndefined()//wrong type was given in Expression
}

func (e Equ) eval(s ValState,level int) Val {
    b1 := e[0].eval(s,level)
    b2 := e[1].eval(s,level)
    switch { //can only check for equality of Vals with same type
    case b1.flag == ValueBool && b1.flag == ValueBool:
        return mkBool(b1.valB == b2.valB)
    case b1.flag == ValueInt && b2.flag == ValueInt:
        return mkBool(b1.valI == b2.valI)
    }
    return mkUndefined() //wrong type was given in either Expression or they are not of the same type
}

func (e Less) eval(s ValState,level int) Val {
    b1 := e[0].eval(s,level)
    b2 := e[1].eval(s,level)
    if(b1.flag == ValueInt && b2.flag == ValueInt){//only ints can be compared with lesser
        return mkBool(b1.valI < b2.valI)
    }
    return mkUndefined()//wrong type was given in either Expression
}

func(e Var) eval (s ValState,level int) Val {
    y := (string)(e)
    for i := level; i >= 0; i-- { //search for var in highest level
        k := key{y,i}
        if b, ok := s[k]; ok {//var exists check for type and return value
        switch{
        case b.flag == ValueBool:
            return mkBool(b.valB)
        case b.flag == ValueInt:
            return mkInt(b.valI)
        }
        return mkUndefined() //Variable is incorrectly typed
        }
    }
    return mkUndefined() //Variable does not exist
}
// Type inferencer/checker

func (x Var) infer(t TyState,level int) Type {
    y := (string)(x)
    for i := level; i >= 0; i-- { //iterate through Val levels from top to bottom
        k := key{y,i}
        if ty, ok := t[k]; ok { //give back type of variable on highest level
            return ty
        }
    }
    return TyIllTyped // variable does not exist yields illtyped
}

func (x Bool) infer(t TyState,level int) Type {
    return TyBool
}

func (x Num) infer(t TyState,level int) Type {
    return TyInt
}

func (e Mult) infer(t TyState,level int) Type {
    t1 := e[0].infer(t,level)
    t2 := e[1].infer(t,level)
    if t1 == TyInt && t2 == TyInt {
        return TyInt
    }
    return TyIllTyped //wrong type was given in either Expression
}

func (e Plus) infer(t TyState,level int) Type {
    t1 := e[0].infer(t,level)
    t2 := e[1].infer(t,level)
    if t1 == TyInt && t2 == TyInt {
        return TyInt
    }
    return TyIllTyped //wrong type was given in either Expression
}

func (e And) infer(t TyState,level int) Type {
    t1 := e[0].infer(t,level)
    t2 := e[1].infer(t,level)
    if t1 == TyBool && t2 == TyBool {
        return TyBool
    }
    return TyIllTyped //wrong type was given in either Expression
}

func (e Or) infer(t TyState,level int) Type {
    t1 := e[0].infer(t,level)
    t2 := e[1].infer(t,level)
    if t1 == TyBool && t2 == TyBool {
        return TyBool
    }
    return TyIllTyped //wrong type was given in either Expression
}

func (e Neg) infer(t TyState,level int) Type {
    t1 := e[0].infer(t,level)
    if t1 == TyBool {
        return TyBool
    }
    return TyIllTyped //wrong type was given in Expression
}

func (e Equ) infer(t TyState,level int) Type {
    t1 := e[0].infer(t,level)
    t2 := e[1].infer(t,level)
    if t1 == TyBool && t2 == TyBool {//can only check for equality of Vals with same type
        return TyBool
    }
    if t1 == TyInt && t2 == TyInt {//can only check for equality of Vals with same type
        return TyBool
    }
    return TyIllTyped //wrong type was given in either Expression or Expressions are not of same type
}

func (e Less) infer(t TyState,level int) Type {
    t1 := e[0].infer(t,level)
    t2 := e[1].infer(t,level )
    if t1 == TyInt && t2 == TyInt {//only ints can be compared with lesser
        return TyInt
    }
    return TyIllTyped //wrong type was given in either Expression
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

func variable(x string) Exp {
    return (Var)(x)
}

//Since Statements are structs, Initialization needs more code
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
    s := make(map[key]Val)
    t := make(map[key]Type)
    fmt.Printf("\n ******* ")
    fmt.Printf("\n %s", e.pretty())
    fmt.Printf("\n %s", showVal(e.eval(s,0)))
    fmt.Printf("\n %s", showType(e.infer(t,0)))
}
//Added, to run Statements
func runSt(st Stmt) {
    s := make(map[key]Val)
    t := make(map[key]Type)
    fmt.Printf("\n ******* ")
    fmt.Printf("\n %s", st.pretty())
    st.eval(s,0) //Statement Evaluation does not give a return, so it is only executed
    fmt.Printf("\n check: %t", st.check(t,0))
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
func st6() { //test for assignment of variables in higher order
    ast := seq(decl("x",boolean(false)),seq(ite(variable("x"),assign("x",boolean(false)),assign("x",boolean(true))),printer(variable("x"))))
    runSt(ast)
}

func st7() { //test for usage of local variables with same names as higher order ones
    ast := seq(decl("x",number(1)),seq(ite(less(variable("x"),number(1)),decl("x",number(2)),decl("x",number(3))),printer(variable("x"))))
    runSt(ast)
}

func st8() { //test for usage of local variables with same names as higher order ones
    ast := seq(decl("x",boolean(true)),seq(while(variable("x"),seq(assign("x",boolean(false)),ite(boolean(true),decl("x",number(1)),decl("x",number(2))))),printer(variable("x"))))
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
    st7()
    st8()
} 
