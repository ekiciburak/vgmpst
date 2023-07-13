open Printf
open Random

type value = 
  | Int : int    -> value
  | Bool: bool   -> value
  | Str : string -> value

let rec value2String(v: value): string =
  match v with
  | Int i  -> string_of_int i
  | Bool b -> string_of_bool b
  | Str s  -> s (*"(val:" ^ s ^ ")"*)

let printValue(v: value): unit =
  printf "%s\n" (value2String v)

type expression = 
  | Val  : value  -> expression
  | EVar : string -> expression
  | Plus : (expression*expression) -> expression
  | Minus: (expression*expression) -> expression
  | Neg  : expression -> expression
  | Eq   : (expression*expression) -> expression
  | Lt   : (expression*expression) -> expression
  | Gt   : (expression*expression) -> expression
  | And  : (expression*expression) -> expression
  | Or   : (expression*expression) -> expression
  | Not  : expression -> expression
  | NDet : (expression*expression) -> expression
  
let rec expression2String(e: expression): string =
  match e with
  | Val v        -> value2String v
  | EVar s       -> s
  | Plus(e1,e2)  -> expression2String e1 ^ "+" ^ expression2String e2
  | Minus(e1,e2) -> expression2String e1 ^ "-" ^ expression2String e2
  | Neg e1       -> "-" ^ expression2String e1
  | Eq(e1,e2)    -> expression2String e1 ^ "=" ^ expression2String e2
  | Lt(e1,e2)    -> expression2String e1 ^ "<" ^ expression2String e2
  | Gt(e1,e2)    -> expression2String e1 ^ ">" ^ expression2String e2
  | And(e1,e2)   -> expression2String e1 ^ "&&" ^ expression2String e2
  | Or(e1,e2)    -> expression2String e1 ^ "||" ^ expression2String e2
  | Not e1       -> "~" ^ expression2String e1
  | NDet(e1,e2)  -> expression2String e1 ^ "⨁" ^ expression2String e2

let printExpression(e: expression): unit =
  printf "%s\n" (expression2String e)

let rec evalExpression(e: expression): expression =
  match e with
  | Val v       -> Val v
  | EVar s      -> EVar s
  | Plus(e1,e2) -> 
    let ee1 = evalExpression e1 in
    let ee2 = evalExpression e2 in
    (
      match (e1,e2) with
      | (Val(Int a1), Val(Int a2)) -> Val(Int(a1+a2))
      | _                          -> Plus(ee1,ee2)
    )
  | Minus(e1,e2) -> 
    let ee1 = evalExpression e1 in
    let ee2 = evalExpression e2 in
    (
      match (e1,e2) with
      | (Val(Int a1), Val(Int a2)) -> Val(Int(a1-a2))
      | _                          -> Minus(ee1,ee2)
    )
  | Neg e1 ->
    let ee1 = evalExpression e1 in
    (
      match ee1 with
      | Val(Int a) -> Val(Int(-a))
      | _          -> Neg ee1
    )
  | Eq(e1,e2) -> 
    let ee1 = evalExpression e1 in
    let ee2 = evalExpression e2 in
    (
      match (e1,e2) with
      | (Val(Int a1), Val(Int a2))   -> Val(Bool(a1=a2))
      | (Val(Bool a1), Val(Bool a2)) -> Val(Bool(a1=a2))
      | (Val(Str a1), Val(Str a2))   -> Val(Bool(a1=a2))
      | _                            -> Eq(ee1,ee2)
    )
  | Lt(e1,e2) -> 
    let ee1 = evalExpression e1 in
    let ee2 = evalExpression e2 in
    (
      match (e1,e2) with
      | (Val(Int a1), Val(Int a2)) -> Val(Bool(a1<a2))
      | _                          -> Lt(ee1,ee2)
    )
  | Gt(e1,e2) -> 
    let ee1 = evalExpression e1 in
    let ee2 = evalExpression e2 in
    (
      match (e1,e2) with
      | (Val(Int a1), Val(Int a2)) -> Val(Bool(a1>a2))
      | _                          -> Gt(ee1,ee2)
    )
  | And(e1,e2) -> 
    let ee1 = evalExpression e1 in
    let ee2 = evalExpression e2 in
    (
      match (e1,e2) with
      | (Val(Bool a1), Val(Bool a2)) -> Val(Bool(a1&&a2))
      | _                            -> And(ee1,ee2)
    )
  | Or(e1,e2) -> 
    let ee1 = evalExpression e1 in
    let ee2 = evalExpression e2 in
    (
      match (e1,e2) with
      | (Val(Bool a1), Val(Bool a2)) -> Val(Bool(a1||a2))
      | _                            -> Or(ee1,ee2)
    )
  | Not e1 ->
    let ee1 = evalExpression e1 in
    (
      match ee1 with
      | Val(Bool a) -> Val(Bool(not a))
      | _           -> Not ee1
    )
  | NDet(e1,e2) ->
    let ee1 = evalExpression e1 in
    let ee2 = evalExpression e2 in
    let v = Random.int 1 in
    if v == 0 then ee1 else ee2 

let rec replaceExpressionE(e:expression) (x:string) (s: expression): expression =
  match e with
  | EVar y       -> if x = y then s else e
  | Plus(e1,e2)  -> Plus(replaceExpressionE e1 x s, replaceExpressionE e2 x s)
  | Minus(e1,e2) -> Minus(replaceExpressionE e1 x s, replaceExpressionE e2 x s)
  | Neg e1       -> Neg(replaceExpressionE e1 x s)
  | Eq(e1,e2)    -> Eq(replaceExpressionE e1 x s, replaceExpressionE e2 x s)
  | Lt(e1,e2)    -> Lt(replaceExpressionE e1 x s, replaceExpressionE e2 x s)
  | Gt(e1,e2)    -> Gt(replaceExpressionE e1 x s, replaceExpressionE e2 x s)
  | And(e1,e2)   -> And(replaceExpressionE e1 x s, replaceExpressionE e2 x s)
  | Or(e1,e2)    -> Or(replaceExpressionE e1 x s, replaceExpressionE e2 x s)
  | Not e1       -> Not(replaceExpressionE e1 x s)
  | NDet(e1,e2)  -> NDet(replaceExpressionE e1 x s, replaceExpressionE e2 x s)
  |_             -> e
