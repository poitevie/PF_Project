(* POITEVIN Eve & REYGNER Etienne *)

(* 1 - Préliminaires théoriques *)

(* 1.1 - Définition et analyse d’un langage de programmation simple *)

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

type v = A | B | C | D;;

type b = Zero | Un;;

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

(* 1.2 - Sémantique Opérationnelle Structurée (SOS) *)

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

type v = A | B | C | D;;

type b = Zero | Un;;

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
let rec terminal c : analist = fun l -> match l with
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

let charOfVariable (v:v): char =
  match v with
  |A -> 'a'
  |B -> 'b'
  |C -> 'c'
  |D -> 'd';;

(* 2.1 - Implémentation de l'interpréteur *)

(* 2.1.1 *)

(* Arbre représentant le programme (décomposé en intructions) *)

type ast =
  | IAssign of v*e
  | ISeq of ast*ast
  | IIf of e*ast*ast
  | IWhile of e*ast
  | IEnd
;;

let rec (parser_v : v ranalist) = fun l -> l |>
                                       (terminal 'a' -+> epsilon_res(A))
                                       +| (terminal 'b' -+> epsilon_res(B))
                                       +| (terminal 'c' -+> epsilon_res(C))
                                       +| (terminal 'd' -+> epsilon_res(D));;

let rec (parser_b : b ranalist) = fun l -> l |>
                                       (terminal '0' -+> epsilon_res(Zero))
                                       +| (terminal '1' -+> epsilon_res(Un));;
let rec (parser_n : n ranalist) = fun l -> l |>
                                             (terminal '#' -+> epsilon_res(N));;

let rec (parser_e : e ranalist) = fun l -> l |>
                                           (parser_v ++> fun a -> epsilon_res(Variable a))
                                           +| (parser_b ++> fun b -> epsilon_res(Booleen b))
                                           +| (parser_n ++> fun c -> epsilon_res(Neg c));;

let rec (parser_s : ast ranalist) = fun l -> l |>
                                               (parser_i ++> fun a -> parser_s ++> fun b -> epsilon_res (ISeq (a, b)))
                                               +| (terminal ';' -+> parser_s)
                                               +| (epsilon_res (IEnd))

and parser_i : ast ranalist = fun l -> l |>
                                         (parser_v ++> fun a -> terminal ':' --> terminal '=' -+> parser_e ++> fun b -> epsilon_res (IAssign ((a, b))))
                                         +| (terminal 'i' --> terminal '(' -+> parser_e ++> fun a -> terminal ')' --> terminal '{' -+> parser_s ++> fun b -> terminal '}' --> terminal '{' -+> parser_s ++> fun c -> terminal '}' -+> parser_s ++> fun d -> epsilon_res (IIf (a, b, c)))
                                               +| (terminal 'w' --> terminal '(' -+> parser_e ++> fun a -> terminal ')' --> terminal '{' -+> parser_s ++> fun b -> terminal '}' -+> parser_s ++> fun c -> epsilon_res (IWhile (a, b)));;

(* 2.1.2 *)

let test s = parser_s (string_to_list s);;

let _ = test "a:=1;w(a){a:=0}";;

(* Test : fonctionne pour la première action *)

(* Création de l'arbre *)
                                         
let crea_ast (s:string) : (ast) = let (ast, cl) = parser_s (string_to_list s) in ISeq (ast, IEnd) ;;

let test2 s = crea_ast s;;

let _ = test2 "a:=1;w(a){a:=0}";;
let _ = test2 "  a:=1;b: =1;c:=1 ;w(a){
i (c){c:=0;a:=b}{b :=0 ;c: =a}}";;

(* Tests OK *)

(* 2.1.3 *)

(* Nous avons modifié la fonction terminal pour accepter les espaces, les indentations et les retours à la ligne *) 

(* 2.2 Mécanique d'état et interpréteur *)

(* 2.2.1 *)

type state =
  | Current of state * char * int
  | End;;

(* Initialisation de l'état *)

let rec init (s:state) = match s with
  | End -> End
  | Current (s', v, x) -> Current (init s', v, 0);;

(* Lire la valeur d'une variable *)

let rec read (s:state) (c:char) : int = match s with
  | End -> raise Echec
  | Current (s', v, x) -> if v = c then x else read s' v;;

(* Modifier la valeur d'une variable *)

let rec assign (s:state) (c:char) (i:int) : state = match s with
  | End -> Current (End, c, i)
  | Current (s', v, x) -> if v = c then Current (s', v, i) else Current (assign s' c i, v, x);;

(* Exécuter une instruction d’affectation (affecter la valeur d'une variable ou une valeur directement *)

let assignInstr (s:state) (v:v) (e:e) : state =
  let c = (charOfVariable v)
  in let x = (match e with
    | Variable v -> (read s (charOfVariable v))
    | Booleen b -> (match b with
                    | Zero -> 0
                    | Un -> 1)
    | Neg n -> (if (read s c) = 0 then 1 else 0)) 
  in assign s c x;;
       
(* 2.2.2 *)

(* Traduit depuis SOS_1 *)

type config =
  | Inter of ast * state
  | Final of state;;

let conditionBool (s:state) (e:e) : bool = (match e with
  | Variable v -> (read s (charOfVariable v)) = 1
  | Booleen b -> (match b with
                    | Zero -> false
                    | Un -> true)
  | Neg n -> raise Echec);;

(* Traduit depuis SOS_1 *)

let rec faire_un_pas c : config = match c with
  | Final s -> Final s
  | Inter (a, s) -> (match a with
                    | IEnd -> Final s
                    | IAssign (v, x) -> Final (assignInstr s v x)
                    | ISeq (a1, a2) -> (match faire_un_pas (Inter (a1, s)) with
                                      | Final s1 -> Inter (a2, s1)
                                      | Inter (a1', s1) -> Inter (ISeq (a1', a2), s1))
                    | IIf (x, a1, a2) -> if (conditionBool s x)
                                        then Inter (a1, s)
                                        else Inter (a2, s)
                    | IWhile (x, a1) -> if (conditionBool s x)
                                    then Inter (ISeq (a1, a), s)
                                    else Final s);;

(* Tests *)

let ast2 = test2 "w(a){a:=0}";;

let start = Inter (ast2, Current(End, 'a', 1));;
let pas = faire_un_pas start;;
let pas = faire_un_pas pas;;
let pas = faire_un_pas pas;;
let pas = faire_un_pas pas;;
let pas = faire_un_pas pas;;
let pas = faire_un_pas pas;;

(* 2.2.3 *)

let rec boucleExecution c : state = match c with
  | Inter (a, s) -> (match a with
                    | IEnd -> s
                    | _ -> boucleExecution (faire_un_pas (Inter (a, s))))
  | Final s -> s;;

(* executer est le cas général du test du dessus *)

let executer (str:string) : state = 
  let ast = test2 str in
  let start = Inter (ast, Current(Current(Current(Current(End, 'd', 0), 'c', 0), 'b', 0), 'a', 0)) in
  boucleExecution start;;

(* Tests *)

let exec = executer "a:=1;b:=1;i(a){d:=1}{c:=1}";;

assert (exec = (Current (Current (Current (Current (End, 'd', 1), 'c', 0), 'b', 1), 'a', 1)));;

let exec = executer "a:=1;b:=1;i(a){a:=#}{c:=1}";;

assert (exec = (Current (Current (Current (Current (End, 'd', 0), 'c', 0), 'b', 1), 'a', 0)));;
