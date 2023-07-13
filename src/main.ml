open Printf
open Expressions
open Processes
open Subst
open Congruence
open Beta
open Types
open Typechecking


let main: unit =
  let pAlice = Send("Bob","l1",Val(Int 50),Receive("Carol",["l3",EVar "x",Inaction])) in
  printProcess pAlice;
  printf "------\n";
  let pBob = Receive("Alice",[("l1",EVar "x",Send("Carol","l2",Val(Int 100),Inaction));("l4",EVar "x",Send("Carol","l2",Val(Int 2),Inaction))]) in
  printProcess pBob;
  printf "------\n";
  let pCarol = Receive("Bob",["l2",EVar "x",Send("Alice","l3",Plus(EVar "x", Val(Int 1)),Inaction)]) in
  printProcess pCarol;
  printf "------\n";
  let s = Comp(Comp(Par("Alice",pAlice),Par("Bob",pBob)),Par("Carol",pCarol)) in
  printSession s;
  printf"-----\n";
  let s = beta s in
  printSession s;
  printf"-----\n";
  let s = beta s in
  printSession s;
  printf"-----\n";
  let s = beta s in
  printSession s;
  printf"-----\n";
  (**)
  let g1 = GMessage("q","r",[("l3",I,GEnd);("l4",N,GEnd)]) in
  printGlobalType g1;
  printf"-----\n";
  let g = GMessage("p","q",[("l1",N,g1);("l2",B,g1)]) in
  printGlobalType g;
  printf"-----\n";
  let gp = projection g "p" in
  printLocalType gp;
  printf"-----\n";
  let gq = projection g "q" in
  printLocalType gq;
  printf"-----\n";
  let gr = projection g "r" in
  printLocalType gr;
  printf"-----\n";
  let g1 = GMessage("q","r",[("l3",I,GEnd);("l5",N,GEnd)]) in
  printGlobalType g1;  
  printf"-----\n"; 
  let g2 = GMessage("q","r",[("l4",I,GEnd);("l5",N,GEnd)]) in
  printGlobalType g2;  
  printf"-----\n";  
  let g = GMessage("p","q",[("l1",N,g1);("l2",B,g2)]) in
  printGlobalType g;  
  printf"-----\n";  
  let gp = projection g "p" in
  printLocalType gp;
  printf"-----\n";
  let gq = projection g "q" in
  printLocalType gq;
  printf"---- defined merging -----\n";
  let gr = projection g "r" in
  printLocalType gr;
  printf"-----\n";  
  let g1 = GMessage("r","q",[("l3",N,GEnd)]) in
  printGlobalType g1;  
  printf"-----\n"; 
  let g2 = GMessage("r","q",[("l4",N,GEnd)]) in
  printGlobalType g2;  
  printf"-----\n"; 
  let g = GMessage("p","q",[("l1",N,g1);("l2",B,g2)]) in
  printGlobalType g;  
  printf"-----\n";
  let gp = projection g "p" in
  printLocalType gp;
  printf"-----\n";
  let gq = projection g "q" in
  printLocalType gq;
  printf"-----\n";
  (*
  printf"-----\n";
  (*undefined merging*)
  let gr = projection g "r" in
  printLocalType gr;
  printf"-----\n";
  *)
  let g1 = GMessage("q","r",[("l3",N,GEnd)]) in
  printGlobalType g1;  
  printf"-----\n"; 

  let g2 = GMessage("q","r",[("l3",N,GMessage("q","r",["l3",N,GEnd]))]) in
  printGlobalType g2;  
  printf"-----\n";  

  let g = GMessage("p","q",[("l1",N,g1);("l2",B,g2)]) in
  printGlobalType g;  
  printf"-----\n";
  let gp = projection g "p" in
  printLocalType gp;
  printf"-----\n";
  let gq = projection g "q" in
  printLocalType gq;
  printf"-----\n";
  (*
  (* undefined merging *)
  printf"-----\n";
  let gr = projection g "r" in
  printLocalType gr;
  printf"-----\n";
  printf"-----\n";
  *)
  printProcess pAlice;
  printf"-----\n";
  printProcess pBob;  
  printf"-----\n";
  printProcess pCarol;
  printf"-----\n";
  let tAlice = typecheck (ConsS("x",I,Nil)) pAlice in
  (
    match tAlice with
    | Yes tAlice' -> printLocalType tAlice'
    | No s        -> failwith s
  );
  printf"-----\n";
  let tBob = typecheck (ConsS("x",I,Nil)) pBob in
  (
    match tBob with
    | Yes tBob' -> printLocalType tBob'
    | No s      -> failwith s
  );
  printf"-----\n";
  let tCarol = typecheck (ConsS("x",I,Nil)) pCarol in
  (
    match tCarol with
    | Yes tCarol' -> printLocalType tCarol'
    | No s        -> failwith s
  );
  printf"-----\n";
  (**)
  let gAdder = GRecursive("t",GMessage("C","S",[("add",I,GMessage("C","S",[("add",I,GMessage("S","C",[("sum",I,GVar "t")]))]));("bye",U,GMessage("S","C",[("bye",U,GEnd)]))])) in
  printGlobalType gAdder;
  printf"-----\n";
  let lC = projection gAdder "C" in
  printLocalType lC;