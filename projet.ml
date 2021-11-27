(* POITEVIN Eve & REYGNER Etienne *)

(* 1 - Préliminaires théoriques *)

(* 1.1.1 *)

(* Grammaire

   Variables :
   V ::= a | b | c | d (variable)
   B ::= 0 | 1 (booléen)
   E ::= N | B (expression)        

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
   E ::= N | B (expression)        

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

   S ::= IL | epsilon (axiome)
   L ::= ;S | epsilon (liste d'instructions)
   I ::= 
   | V:=E 
   | i(E){S}{S} 
   | w(E){S}    
   | epsilon
   
 *)

(* Nouveau type i *)

type s =
  | Axiome of i * l
  | EpsilonS
and
  l =
  | ListeInstructions of s
  | EpsilonL
and
  i =
  | Affectation of v * e
  | While of e * s
  | If of e * s * s
  | EpsilonI;;
