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

   S ::= I;S
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
                                    | x :: l when x = ' ' -> terminal c l
                                    | x :: l when x = '\t' -> terminal c l
                                    | x :: l when x = '\n' -> terminal c l
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

type ast =
  | PA of v*e
  | PS of ast*ast
  | PI of e*ast*ast
  | PW of e*ast
  | PEpsilon
;;

let rec (parser_v : v ranalist) = fun l -> l |>
                                       (terminal 'a' -+> epsilon_res(A))
                                       +| (terminal 'b' -+> epsilon_res(B))
                                       +| (terminal 'c' -+> epsilon_res(C))
                                       +| (terminal 'd' -+> epsilon_res(D));;

let rec (parser_b : b ranalist) = fun l -> l |>
                                       (terminal '0' -+> epsilon_res(Zero))
                                       +| (terminal '1' -+> epsilon_res(Un));;

let rec (parser_e : e ranalist) = fun l -> l |>
                                           (parser_v ++> fun a -> epsilon_res(Variable a))
                                           +| (parser_b ++> fun b -> epsilon_res(Booleen b));;

let rec (parser_a : ast ranalist) = fun l -> l |>
                                               (parser_v ++> fun a -> terminal ':' --> terminal '=' -+> parser_e ++> fun b -> epsilon_res (PA ((a, b))));;

let rec (parser_s : ast ranalist) = fun l -> l |>
                                               (parser_i ++> fun a -> epsilon_res (a))
                                               +| (epsilon_res (PEpsilon))

and parser_i : ast ranalist = fun l -> l |>
                                               (parser_a ++> fun a -> terminal ';' -+> parser_s ++> fun b -> epsilon_res (PS ((a, b))))
                                               +| (terminal 'i' --> terminal '(' -+> parser_e ++> fun a -> terminal ')' --> terminal '{' -+> parser_s ++> fun b -> terminal '}' --> terminal '{' -+> parser_s ++> fun c -> terminal '}' -+> parser_s ++> fun d -> epsilon_res (PS ((PI (a, b, c)), d)))
                                               +| (terminal 'w' --> terminal '(' -+> parser_e ++> fun a -> terminal ')' --> terminal '{' -+> parser_s ++> fun b -> terminal '}' -+> parser_s ++> fun c -> epsilon_res (PS ((PW (a, b)), c)));;

(* 2.1.2 *)

(* Test : fonctionne pour la première action *)
let test s = parser_s (string_to_list s);;

let _ = test "a:=1;w(a){a:=0}";;

(* Récupération uniquement de l'AST et réécriture sous la forme d'un seq*)
                                         
let crea_ast (s:string) : (ast) = let (ast, cl) = parser_s (string_to_list s) in PS (ast, PEpsilon) ;;

let test2 s = crea_ast s;;

let _ = test2 "a:=1;w(a){a:=0;}";;
let _ = test2 "  a:=1;b: =1;c:=1 ;w(a)
{i (c){c:=0;a:=b;}{b :=0 ;c: =a;}}";;

(* 2.1.3 *)

(* Nous avons modifié la fonction terminal pour accepter les espaces, les indentations et les retours à la ligne *)

