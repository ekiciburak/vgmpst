open Printf
open Expressions

type participant = string 

let printParticipant(p: participant): unit =
  printf "%s\n" p

type label = string

type process = 
  | PVar       : string                                 -> process
  | Inaction   : process
  | Send       : (participant*label*expression*process) -> process
  | Receive    : (participant*procList)                 -> process
  | Conditional: (expression*process*process)           -> process
  | Recursion  : (string*process)                       -> process
and procList = (label*expression*process) list

let rec process2String(p: process): string =
  match p with
  | Inaction             -> "O"
  | PVar s               -> s
  | Send(par,l,e,p1)     -> par ^ "!" ^ l ^ "<" ^ expression2String e ^ ">." ^ process2String p1
  | Receive(par,l)       -> procList2String par l
                            (*"Σ " ^ par ^ "?" ^ procList2String l*)
  | Conditional(e,p1,p2) -> "if " ^ expression2String e ^ " then " ^ process2String p1 ^ " else " ^ process2String p2
  | Recursion(s,p1)      -> "µ" ^ s ^ "." ^ process2String p1
and procList2String par l =
  match l with
  | []          -> ""
  | [(x,e,y)]   -> par ^ "?" ^  x ^ "(" ^ expression2String e ^ ")." ^  process2String y
  | (x,e,y)::xs -> par ^ "?" ^  x ^ "(" ^ expression2String e ^ ")." ^  process2String y ^ " + " ^ procList2String par xs

let printProcess(p: process): unit =
  printf "%s\n" (process2String p)

type session =
  | Par : (participant*process) -> session 
  | Comp: (session*session)     -> session

let rec session2String(s: session): string =
  match s with
  | Par(par,p)  -> par ^ "::" ^ process2String p
  | Comp(s1,s2) -> session2String s1 ^ " |\n" ^ session2String s2

let printSession(s: session): unit =
  printf "%s\n" (session2String s)