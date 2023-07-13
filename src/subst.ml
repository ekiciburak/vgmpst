open Printf
open Expressions
open Processes

let rec find(y: string) (l: string list): bool =
  match l with
  | []    -> false
  | x::xs -> if x = y then true else find y xs

let rec uniqueH(l: string list) (acc: string list): string list =
  match l with
  | []    -> acc
  | x::xs -> if find x acc then uniqueH xs acc else uniqueH xs (acc @ [x])

let unique(l: string list): string list =
  uniqueH l []

let rec find(y: string) (l: string list): bool =
  match l with
  | []    -> false
  | x::xs -> if x = y then true else find y xs

let rec fvH(e: process) (acc: string list): string list =
  match e with
  | PVar x                -> x :: acc
  | Send(par,l,e1,p1)     -> fvH p1 acc
  | Receive(par,l)        -> fvHB l acc
  | Conditional(e1,p1,p2) -> fvH p1 acc @ fvH p2 acc
  | Recursion(y,p1)       -> List.filter (fun a -> a != y) (fvH p1 acc)
  | _                     -> acc
and fvHB l acc =
  match l with
  | []           -> acc
  | (y,e,p1)::xs -> fvH p1 acc @ fvHB xs acc

let fv(t: process): string list =
  unique(fvH t [])

let rec replace(e: process) (x: string) (s: process): process =
  match e with
  | Inaction              -> Inaction
  | PVar y                -> if x = y then s else e
  | Send(par,l,e1,p1)     -> Send(par,l,e1,replace p1 x s)
  | Receive(par,l)        -> Receive(par,replaceProcList l x s)
  | Conditional(e1,p1,p2) -> Conditional(e1,replace p1 x s, replace p2 x s)
  | Recursion(y,p1)       -> if (y != x) && (find y (fv s) = false) then 
                             Recursion(y,replace p1 x s) else e                          
and replaceProcList l x s =
  match l with
  | []           -> []
  | (y,e,p1)::xs -> (y,e,replace p1 x s) :: replaceProcList xs x s

let rec replaceExpression(e: process) (x: string) (s: expression): process =
  match e with
  | Send(par,l,y,p1)     -> Send(par,l,replaceExpressionE y x s,replaceExpression p1 x s) 
  | Receive(par,l)       -> Receive(par,replaceExpressionProcList l x s)
  | Conditional(y,p1,p2) -> Conditional(replaceExpressionE y x s,replaceExpression p1 x s, replaceExpression p2 x s)
  | Recursion(y,p1)      -> (* if y != x && find y (fv s) = false then *)
    Recursion(y,replaceExpression p1 x s) (* else e *)
  | _                    -> e
and replaceExpressionProcList l x s =
  match l with
  | []           -> []
  | (y,e,p1)::xs -> (y,replaceExpressionE e x s,replaceExpression p1 x s) :: replaceExpressionProcList xs x s 
  

