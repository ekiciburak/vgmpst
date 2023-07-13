open Printf
open Expressions
open Processes
open Subst
open Congruence

let rec findProcess (l:procList) (lbl: label): (expression*process) =
  match l with
  | []              -> failwith "no such process found! -- beta"
  | (l1,e1,p) :: xs -> if l1 = lbl then (e1,p) else findProcess xs lbl

let rec beta(s: session): session =
  match s with
  | Comp(Comp(Par(p1,Recursion(x,p)),s1),s2) -> 
    Comp(Comp(Par(p1,replace p x (Recursion(x,p))),s1),s2)

  | Comp(Comp(s1,Par(p1,Recursion(x,p))),s2) -> 
    Comp(Comp(s1,Par(p1,replace p x (Recursion(x,p)))),s2)

  | Comp(Comp(s1,s2),Par(p1,Recursion(x,p))) -> 
    Comp(Comp(s1,s2),Par(p1,replace p x (Recursion(x,p))))
  
  (**)
  
  | Comp(Comp(Par(p1,Send(q1,lbl,e,proc1)),Par(q2,Receive(p2,l))),s1) when p1 = p2 && q1 = q2 && p1 != q1 ->
    let v = evalExpression e in
    let (e',proc2) = findProcess l lbl in
    (
      match e' with
      | EVar x ->  Comp(Comp(Par(p1,proc1),Par(q2,replaceExpression proc2 x v)),s1)
      | _      -> failwith "beta sr1"
    )
  
  | Comp(Comp(Par(p1,Send(q1,lbl,e,proc1)),s1),Par(q2,Receive(p2,l))) when p1 = p2 && q1 = q2 && p1 != q1 ->
    let v = evalExpression e in
    let (e',proc2) = findProcess l lbl in
    (
      match e' with
      | EVar x -> Comp(Comp(Par(p1,proc1),s1),Par(q2,replaceExpression proc2 x v))
      | _      -> failwith "beta sr2"
    )
    
  | Comp(Comp(s1,Par(p1,Send(q1,lbl,e,proc1))),Par(q2,Receive(p2,l))) when p1 = p2 && q1 = q2 && p1 != q1 ->
    let v = evalExpression e in
    let (e',proc2) = findProcess l lbl in
    (
      match e' with
      | EVar x -> Comp(Comp(s1,Par(p1,proc1)),Par(q2,replaceExpression proc2 x v))
      | _      -> failwith "beta sr3"
    )  

  (**)

  | Comp(Comp(Par(q2,Receive(p2,l)),Par(p1,Send(q1,lbl,e,proc1))),s1) when p1 = p2 && q1 = q2 && p1 != q1 ->
    let v = evalExpression e in
    let (e',proc2) = findProcess l lbl in
    (
      match e' with
      | EVar x -> Comp(Comp(Par(q2,replaceExpression proc2 x v),Par(p1,proc1)),s1)
      | _      -> failwith "beta rs1"
    )  

  
  | Comp(Comp(Par(q2,Receive(p2,l)),s1),Par(p1,Send(q1,lbl,e,proc1))) when p1 = p2 && q1 = q2 && p1 != q1 ->
    let v = evalExpression e in
    let (e',proc2) = findProcess l lbl in
    (
      match e' with
      | EVar x -> Comp(Comp(Par(q2,replaceExpression proc2 x v),s1),Par(p1,proc1))
      | _      -> failwith "beta rs2"
    )  
  
  | Comp(Comp(s1,Par(q2,Receive(p2,l))),Par(p1,Send(q1,lbl,e,proc1))) when p1 = p2 && q1 = q2 && p1 != q1 ->
    let v = evalExpression e in
    let (e',proc2) = findProcess l lbl in
    (
      match e' with
      | EVar x -> Comp(Comp(s1,Par(q2,replaceExpression proc2 x v)),Par(p1,proc1))
      | _      -> failwith "beta rs3"
    )  

  (**)

  | Comp(Comp(s1,Par(p1,Conditional(e,proc1,proc2))),s2) ->
    let v = evalExpression e in
    (
      match v with
      | Val(Bool true)  -> Comp(Comp(s1,Par(p1,proc1)),s2)
      | Val(Bool false) -> Comp(Comp(s1,Par(p1,proc2)),s2)
      | _               -> Comp(Comp(s1,Par(p1,Conditional(v,proc1,proc2))),s2)
    )
  | Comp(Comp(Par(p1,Conditional(e,proc1,proc2)),s1),s2) ->
    let v = evalExpression e in
    (
      match v with
      | Val(Bool true)  -> Comp(Comp(Par(p1,proc1),s1),s2)
      | Val(Bool false) -> Comp(Comp(Par(p1,proc2),s1),s2)
      | _               -> Comp(Comp(Par(p1,Conditional(v,proc1,proc2)),s1),s2)
    )
  | Comp(Comp(s1,s2),Par(p1,Conditional(e,proc1,proc2))) ->
    let v = evalExpression e in
    (
      match v with
      | Val(Bool true)  -> Comp(Comp(s1,s2),Par(p1,proc1))
      | Val(Bool false) -> Comp(Comp(s1,s2),Par(p1,proc2))
      | _               -> Comp(Comp(s1,s2),Par(p1,Conditional(v,proc1,proc2)))
    )
  (*
  | Comp(Comp(s1,s2),s3) -> Comp(s1,Comp(s2,s3))
  | Comp(s1,s2)          -> Comp(s2,s1)
  *)

  | _ -> failwith "nope"
