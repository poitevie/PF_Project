(* POITEVIN Eve & REYGNER Etienne *)

(* 1 - Préliminaires théoriques *)

(* 1.1.1 *)

(* Grammaire

   Variables :
   V ::= a | b | c | d (variable)
   B ::= 0 | 1 (booléen)
   E ::= V | B (expression)        

   Instructions :
   I ::=
     | I;I
     | V:=E
     | w(E){I}
     | i(E){I}{I}
     | epsilon
     
 *)

type v =
  | A
  | B
  | C
  | D;;

type b =
  | Zero
  | Un;;

type e =
  | Variable of v
  | Booleen of b;;

type i =
  | Sequence of i * i
  | Affectation of v * e
  | While of e * i
  | If of e * i * i
  | EpsilonI;;

(* 1.1.2 *)

(* Grammaire

   Variables :
   V ::= a | b | c | d (variable)
   B ::= 0 | 1 (booléen)
   E ::= V | B (expression)        

   Instructions :
   I ::=
     | I;I
     | V:=E
     | w(E){I}
     | i(E){I}{I}
     | epsilon
     
 *)

(* 1.1.3 *)

(* Nouvelle grammaire

   Variables :
   V ::= a | b | c | d (variable)
   B ::= 0 | 1 (booléen)
   E ::= N | B (expression)        

   Instructions :

   S ::= I;S | epsilon (axiome)
   I ::= 
   | V:=E 
   | i(E){S}{S} 
   | w(E){S}    
   | epsilon
   
 *)

(* Nouveau type i *)

type s =
  | Axiome of i * s
  | EpsilonS
and
  i =
  | Affectation of v * e
  | While of e * s
  | If of e * s * s
  | EpsilonI;;

(* 1.2.1 *)

(*
[[expr]]_s == true                               [[expr]]_s == false
---------------------------------                ---------------------------------
s, (if expr then P else Q) -> s,(P)              s, (if expr then P else Q) -> s,(Q)
 *)

(* 1.2.2 *)

(* Nouvelle grammaire où on ajoute la négation

   Variables :
   V ::= a | b | c | d (variable)
   B ::= 0 | 1 (booléen)
   E ::= V | B | N (expression)        

   Instructions :

   S ::= I;I
   I ::= 
   | V:=E 
   | i(E){S}{S} 
   | w(E){S}    
   | epsilon
   
 *)

type v =
  | A
  | B
  | C
  | D;;

type b =
  | Zero
  | Un;;

type n =
  | N;;

type e =
  | Variable of v
  | Booleen of b
  | Neg of n;;

type s =
  | Axiome of i * s
  | EpsilonS
and
  i =
  | Assign of v * e
  | Seq of s * s
  | While of e * s
  | If of e * s * s
  | EpsilonI;;

(* 2 - Partie principale *)

let string_to_list s =
  let n = String.length s in
  let rec boucle i =
    if i = n then [] else s.[i] :: boucle (i+1)
  in boucle 0
;;

type analist = char list -> char list

type 'res ranalist = char list -> 'res * char list

exception Echec

(* terminal constant *)
let terminal c : analist = fun l -> match l with
  | x :: l when x = c -> l
  | _ -> raise Echec

(* terminal conditionnel *)
let terminal_cond (p : 'term -> bool) : analist = function
  | x :: l when p x -> l
  | _ -> raise Echec

(* non-terminal vide *)
let epsilon : analist = fun l -> l

(* Composition séquentielle : a suivi de b *)
let (-->) (a : analist) (b : analist) : analist =
  fun l -> let l = a l in b l

(* Choix entre a ou b *)
let (-|) (a : analist) (b : analist) : analist =
  fun l -> try a l with Echec -> b l

let epsilon_res (info : 'res) : 'res ranalist =
  fun l -> (info, l)

let terminal_res (f : char -> 'res option) : 'res ranalist =
  fun l -> match l with
    | x :: l -> (match f x with Some y -> y, l | None -> raise Echec)
    | _ -> raise Echec

(* Choix entre a ou b informatifs *)
let (+|) (a : 'res ranalist) (b : 'res ranalist) : 'res ranalist =
  fun l -> try a l with Echec -> b l

(* a sans résultat suivi de b donnant un résultat *)
let ( -+>) (a : analist) (b : 'res ranalist) : 'res ranalist =
  fun l -> let l = a l in b l

(* a rendant un résultat suivi de b sans résultat *)
let (+->) (a : 'res ranalist) (b : analist) : analist =
  fun l -> let (x, l) = a l in b l

(* a rendant un résultat suivi de b rendant un résultat *)
let (++>) (a : 'resa ranalist) (b : 'resa -> 'resb ranalist) : 'resb ranalist =
  fun l -> let (x, l) = a l in b x l
;;


(* 2.1.1 *)

let rec (parser_v : ranalist) = fun l -> l |>
                                       (terminal 'a' -+> epsilon_res(A))
                                       +| (terminal 'b' -+> epsilon_res(B))
                                       +| (terminal 'c' -+> epsilon_res(C))
                                       +| (terminal 'd' -+> epsilon_res(D));;

let rec (parser_b : ranalist) = fun l -> l |>
                                       (terminal '0' -+> epsilon_res(Zero))
                                       +| (terminal '1' -+> epsilon_res(Un));;

let rec (parser_e : ranalist) = fun l -> l |>
                                           (parser_v ++> fun a -> epsilon_res(Variable a))
                                           +| (parser_b ++> fun b -> epsilon_res(Booleen b));;

let test s = parser_e(string_to_list s);;
let _ = test "a";;
