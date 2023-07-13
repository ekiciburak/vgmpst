open Printf
open Expressions
open Processes
open Subst

let isCongruenceProcess(p1: process) (p2: process): bool =
  match p1 with
  | Recursion(y1,p3) -> p2 = replace p3 y1 (Recursion(y1,p3))
  | _                -> false

let rec congruenceProcessH(p: process) (n: int) (acc: process): process =
  match p with
  | Recursion(y1,p1) -> if n > 0 
                        then congruenceProcessH p (n-1) (replace acc y1 p)
                        else acc
  | _                -> p
  
let congruenceProcess(p: process) (n: int): process =
  match p with
  | Recursion(y,p1) -> congruenceProcessH p n p1
  | _               -> p

let rec isCongruenceSession(s:session): session =
  match s with
  | Comp(Par(par,Inaction),s1) -> s1 
  | Comp(s1,Comp(s2,s3))       -> Comp(Comp(s1,s2),s3) 
  | Comp(s1,s2)                -> Comp(s2,s1)
  | _                          -> s
