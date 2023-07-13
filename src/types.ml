open Printf
open Expressions
open Processes
open Subst
open Congruence
open Beta

type sort = 
  | I: sort
  | N: sort
  | B: sort
  | S: sort
  | U: sort

let rec sort2String(s: sort): string =
  match s with
  | I -> "int"
  | N -> "nat"
  | B -> "bool"
  | S -> "string"
  | U -> ""

let printSort(s: sort): unit =
  printf "%s\n" (sort2String s)

type globalType =
  | GEnd      : globalType
  | GMessage  : (participant*participant*labelGT) -> globalType
  | GRecursive: (string*globalType)               -> globalType
  | GVar      : string                            -> globalType
and labelGT = (label*sort*globalType) list   

let rec globalType2String(g: globalType): string =
  match g with
  | GEnd              -> "g_end"
  | GMessage(p1,p2,l) -> p1 ^ "->" ^ p2 ^ ":{" ^ labelGT2String l ^ "}"
  | GRecursive(s,g1)  -> "µ" ^ s ^ "." ^ globalType2String g1
  | GVar s            -> s
and labelGT2String l =
  match l with
  | []             -> ""
  | [(lbl,s,g1)]   -> lbl ^ "(" ^ sort2String s ^ ")." ^ globalType2String g1 
  | (lbl,s,g1)::xs -> lbl ^ "(" ^ sort2String s ^ ")." ^ globalType2String g1 ^ "; " ^ labelGT2String xs

let printGlobalType(g: globalType): unit =
  printf "%s\n" (globalType2String g)

type localType =
  | LEnd      : localType
  | LSelection: (participant*labelLT) -> localType
  | LBranch   : (participant*labelLT) -> localType
  | LVar      : label                 -> localType
  | LRecursion: (label*localType)     -> localType
and labelLT = (label*sort*localType) list

let rec localType2String(t: localType): string =
  match t with
  | LEnd               -> "l_end"
  | LSelection(par,l)  -> "(" ^ labelLT2String l "⨁" "!" par ^ ")"
  | LBranch(par,l)     -> "(" ^ labelLT2String l "&" "?" par ^ ")"
  | LVar s             -> s
  | LRecursion(s,t1)   -> "µ" ^ s ^ "." ^ localType2String t1
and labelLT2String l str str2 par =
  match l with
  | []        -> ""
  | [(x,s,y)]   -> par ^ str2 ^ x ^ "(" ^ sort2String s ^ ")." ^  localType2String y
  | (x,s,y)::xs -> par ^ str2 ^ x ^ "(" ^ sort2String s ^ ")." ^  localType2String y ^ " " ^ str ^ " " ^ labelLT2String xs str str2 par

let printLocalType(s: localType): unit =
  printf "%s\n" (localType2String s)

(**)

let rec find(y: participant) (l: participant list): bool =
  match l with
  | []    -> false
  | x::xs -> if x = y then true else find y xs

let rec uniqueH(l: participant list) (acc: participant list): participant list =
  match l with
  | []    -> acc
  | x::xs -> if find x acc then uniqueH xs acc else uniqueH xs (acc @ [x])

let unique(l: participant list): participant list =
  uniqueH l []

let rec globalParticipantList2String(l: participant list): participant =
  match l with
  | []    -> ""
  | [x]   -> x
  | x::xs -> x ^ "," ^ globalParticipantList2String xs

let printGlobalParticipantList(l: participant list): unit =
  printf("[%s]\n") (globalParticipantList2String l)
    
let rec participantsGTH(g: globalType) (acc: participant list) : participant list =
  match g with
  | GEnd              -> acc
  | GVar s            -> acc
  | GMessage(p1,p2,l) -> unique(p1::p2::labelGP l acc)
  | GRecursive(s,g1)  -> unique(participantsGTH g1 acc)
and labelGP l acc =
  match l with
  | []            -> acc
  | (lbls,s,g1):: xs -> (participantsGTH g1 acc) @ (labelGP xs acc)
  
let participantsGT(g: globalType): participant list =
  unique(participantsGTH g [])

(**)

let rec findLT(y: (label*sort*localType)) (l: labelLT): bool =
  match l with
  | []    -> false
  | x::xs -> if x = y then true else findLT y xs

let rec uniqueLTH(l: labelLT) (acc: labelLT): labelLT =
  match l with
  | []    -> acc
  | x::xs -> if findLT x acc then uniqueLTH xs acc else uniqueLTH xs (acc @ [x])

let uniqueLT(l: labelLT): labelLT =
  uniqueLTH l []

let rec mergeLT(l1: labelLT) (l2: labelLT): labelLT =
  match l1 with
  | []    -> l2
  | x::xs -> x :: mergeLT xs l2

let rec mergeLTA(l1: labelLT) (l2: labelLT) (acc: labelLT): labelLT =
  match l1 with
  | [] -> acc
  | (lbl1,s1,t1)::xs ->
    let rec mergeLTB l1 l2 acc =
      match l2 with
      | []               -> mergeLTA xs l2 (acc @ [(lbl1,s1,t1)])
      | (lbl2,s2,t2)::ys -> if lbl1 = lbl2 && s1 = s2 && t1 = t2 
                            then mergeLTA xs ys (acc @ [(lbl1,s1,t1)]) 
                            else if lbl1 != lbl2 then mergeLTA xs ys (acc @ [(lbl1,s1,t1)] @ [(lbl2,s2,t2)]) 
                            else if lbl1 = lbl2 && s1 = s2 && t1 != t2
                            then failwith "undefined merging -- 2"
                            else mergeLTA l1 ys acc
    in mergeLTB l1 l2 acc


let merging(lt1: localType) (lt2: localType): localType =
  if lt1 = lt2 then lt1
  else
    (
      match (lt1,lt2) with
      | (LBranch(p1,lst1),LBranch(p2,lst2)) when p1 = p2 -> LBranch(p1,uniqueLT(mergeLTA lst1 lst2 []))
      | _ -> failwith "undefined merging -- 1"
    )

let rec mergeList(l: labelLT): localType = 
  match l with
  | []             -> LEnd
  | [(lbl,s,lt)]   -> lt
  | (lbl,s,lt)::xs -> merging lt (mergeList xs) 

let rec isLocalsSameH(l: labelLT) (m: (label*sort*localType)): bool =
  match (l,m) with
  | ([],_)                         -> true
  | ((lbl1,s1,l1)::xs,(mlbl,s,ml)) -> if l1 = ml then isLocalsSameH xs m else false

let rec isLocalsSame(l: labelLT): bool =
  match l with
  | []              -> true
  | (lbl,s1,l1)::xs -> isLocalsSameH xs (lbl,s1,l1) 

let rec projection(g: globalType) (r: participant): localType =
  match g with
  | GEnd               -> LEnd
  | GVar s             -> LVar s
  | GMessage(p1,p2,l) -> if p1 = r then LSelection(p2,labelLT l r)
                         else if p2 = r then LBranch(p1,labelLT l r)
                         else if p1 != r && p2 != r (* && isLocalsSame (labelLT l r)*)
                         (*then woLabelLT l r*)
                         then mergeList (labelLT l r)
                         else failwith "undefined -- branching proj 1"
  | GRecursive(s,g1)  -> if find r (participantsGT g1) = false (* && fv g = [] *)
                         then LEnd
                         else LRecursion(s,projection g1 r)
and labelLT l r =
  match l with
  | []              -> []
  | (lbl,s1,g1)::xs -> (lbl,s1,projection g1 r) :: labelLT xs r
and woLabelLT l r =
  match l with
  | []              -> failwith "undefined -- branching proj 2"
  | (lbl,s1,g1)::xs -> projection g1 r 

