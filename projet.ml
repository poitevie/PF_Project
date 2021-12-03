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
  | Booleen of b;;
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
