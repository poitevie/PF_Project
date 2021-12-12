(* POITEVIN Eve & REYGNER Etienne *)

Require Import Bool Arith List.
Import List.ListNotations.

(* ----- 2.3 Preuves sur la SN -----*)

(** ** Syntaxe des expressions arithétiques *)

Inductive aexp :=
| Aco : nat -> aexp (* constantes *)
| Ava : nat -> aexp (* variables *)
| Apl : aexp -> aexp -> aexp
| Amu : aexp -> aexp -> aexp
| Amo : aexp -> aexp -> aexp
.

(** ** Syntaxe des expressions booléennes *)

Inductive bexp :=
| Btrue : bexp
| Bfalse : bexp
| Bnot : bexp -> bexp
| Band : bexp -> bexp -> bexp
| Bor : bexp -> bexp -> bexp
| Beq : bexp -> bexp -> bexp (* test égalité de bexp *)
| Beqnat : aexp -> aexp -> bexp (* test égalité d'aexp *)
.

(** ** Syntaxe du langage impératif WHILE *)

Inductive winstr :=
| Skip   : winstr
| Assign : nat -> aexp -> winstr
| Seq    : winstr -> winstr -> winstr
| If     : bexp -> winstr -> winstr -> winstr
| While  : bexp -> winstr -> winstr
.

(** ** Quelques listes/états pour faire des tests *)
(** S1 est un état dans lequel la variable '0' vaut 1 et la variable '1' vaut 2
    et toutes les autres '0' (valeur par défaut)                             *)
(** Une variable (Ava i) étant représentée par un entier naturel i,
    sa valeur dans l'état est la valeur de la ieme position de la liste *)

Definition state := list nat.

Definition S1 := [1; 2].
Definition S2 := [0; 3].
Definition S3 := [0; 7; 5; 41].

(** * Sémantique *)
(** On reprend les sémantiques fonctionnelles
    des expressions artihmétiques et booléennes      *)

(** La fonction get x s rend la valeur de x dans s. *)
(** Elle rend 0 par défaut, par exemple si la variable
    n'est pas définie/initialisée    *)

Fixpoint get (x:nat) (s:state) : nat :=
match x,s with
| 0   , v::_      => v
| S x1, _::l1 => get x1 l1
| _   , _         => 0
end.

(** La mise à jour d'une variable v par un nouvel entier n dans un état s
    s'écrit 'update s v n'
    Cette fonction n'échoue jamais et écrit la valeur à sa place même
    si elle n'est pas encore définie dans l'état *)

Fixpoint update (s:state) (v:nat) (n:nat): state :=
  match v,s with
  | 0   , a :: l1 => n :: l1
  | 0   , nil     => n :: nil
  | S v1, a :: l1 => a :: (update l1 v1 n)
  | S v1, nil     => 0 :: (update nil v1 n)
  end.

(** ** Sémantique fonctionnelle de aexp*)
Fixpoint evalA (a: aexp) (s: state) : nat :=
  match a with
  | Aco n => n
  | Ava x => get x s
  | Apl a1 a2 =>  evalA a1 s + evalA a2 s
  | Amu a1 a2 =>  evalA a1 s * evalA a2 s
  | Amo a1 a2 =>  evalA a1 s - evalA a2 s
  end.

(** ** Sémantique fonctionnelle de Baexp*)

Definition eqboolb b1 b2 : bool :=
  match b1, b2  with
  | true , true  => true
  | false, false => true
  | _    , _     => false
  end.

Fixpoint eqnatb n1 n2 : bool :=
  match n1, n2 with
  | O    , O     => true
  | S n1', S n2' => eqnatb n1' n2'
  | _    , _     => false
  end.

Fixpoint evalB (b : bexp) (s : state) : bool :=
  match b with
  | Btrue => true
  | Bfalse => false
  | Bnot b => negb (evalB b s)
  | Band e1 e2 => (evalB e1 s) && (evalB e2 s)
  | Bor e1 e2 => (evalB e1 s) || (evalB e2 s)
  | Beq e1 e2 => eqboolb (evalB e1 s) (evalB e2 s)
  | Beqnat n1 n2 => eqnatb (evalA n1 s) (evalA n2 s)
  end.

(** Pour définir plus facilement des expressions de test on prédéfinit
    des constantes entières ... *)

Definition N0 := Aco 0.
Definition N1 := Aco 1.
Definition N2 := Aco 2.
Definition N3 := Aco 3.
Definition N4 := Aco 4.

(** ...  et des variables *)

Definition X := Ava 1.
Definition Y := Ava 2.
Definition Z := Ava 3.


(** Quelques expressions arithmétiques pour tester *)

(** exp1 = x + 3 *)
Definition E1 := Apl X N3.

(** exp2 = y - 1 *)
Definition E2 := Amo Y N1.

(** exp3 = (x + y) * 2 *)
Definition E3 := Amu (Apl X Y) N2.


(** ** Version relationnelle, appelée "sémantique naturelle" *)

(** Vu dans le CM précédent.
    La sémantique naturelle (ou sémantique opérationnelle à grands pas)
    du langage WHILE est donnée sous la forme d'un prédicat inductif. *)

Inductive SN: winstr -> state -> state -> Prop :=
| SN_Skip        : forall s,
                   SN Skip s s
| SN_Assign      : forall x a s,
                   SN (Assign x a) s (update s x (evalA a s))
| SN_Seq         : forall i1 i2 s s1 s2,
                   SN i1 s s1 -> SN i2 s1 s2 -> SN (Seq i1 i2) s s2
| SN_If_true     : forall b i1 i2 s s1,
                   (evalB b s = true)  ->  SN i1 s s1 -> SN (If b i1 i2) s s1
| SN_If_false    : forall b i1 i2 s s2,
                   (evalB b s = false) ->  SN i2 s s2 -> SN (If b i1 i2) s s2
| SN_While_false : forall b i s,
                   (evalB b s = false) ->  SN (While b i) s s
| SN_While_true  : forall b i s s1 s2,
                   (evalB b s = true)  ->  SN i s s1 -> SN (While b i) s1 s2 ->
                   SN (While b i) s s2
.

(** *** Illustration *)
(** Une autre manière d'exprimer la sémantique de WHILE ;
    on prouvera que SN et SN' sont équivalentes. *)
Inductive SN': winstr -> state -> state -> Prop :=
| SN'_Skip        : forall s,
                    SN' Skip s s
| SN'_Assign      : forall x a s,
                    SN' (Assign x a) s (update s x (evalA a s))
| SN'_Seq         : forall i1 i2 s s1 s2,
                    SN' i1 s s1 -> SN' i2 s1 s2 -> SN' (Seq i1 i2) s s2
| SN'_If_true     : forall b i1 i2 s s1,
                    (evalB b s = true)  ->  SN' i1 s s1 -> SN' (If b i1 i2) s s1
| SN'_If_false    : forall b i1 i2 s s2,
                    (evalB b s = false) ->  SN' i2 s s2 -> SN' (If b i1 i2) s s2
| SN'_While_false : forall b i s,
                    (evalB b s = false) ->  SN' (While b i) s s
| SN'_While_true  : forall b i s s1,
                    (evalB b s = true)  ->  SN' (Seq i (While b i)) s s1 ->
                    SN' (While b i) s s1
.

(** On code dans WHILE un programme P1 correspondant à
    while not (i=0) do {i:=i-1;x:=1+x} *)
Definition Il := 0.
Definition Ir := Ava Il.
Definition Xl := 1.
Definition Xr := Ava Xl.

Definition corps_boucle := Seq (Assign Il (Amo Ir N1)) (Assign Xl (Apl N1 Xr)).
Definition P1 := While (Bnot (Beqnat Ir N0)) corps_boucle.


(** *** Calcul du carré avec des additions *)
(** On code dans While un programme Pcarre correspondant à
    while not (i=n) do {i:= 1+i; x:= y+x ; y:= 2+y} *)
(* (* *déjà définis *)
Definition Il := 0.
Definition Ir := Ava Il.
Definition Xl := 1.
Definition Xr := Ava Xl.*)
Definition Yl := 2.
Definition Yr := Ava Yl.

Definition incrI := Assign Il (Apl N1 Ir).
Definition incrX := Assign Xl (Apl Yr Xr).
Definition incrY := Assign Yl (Apl N2 Yr).
Definition corps_carre := Seq incrI (Seq incrX incrY).
Definition Pcarre_2 := While (Bnot (Beqnat Ir (Aco 2))) corps_carre.
Definition Pcarre n := While (Bnot (Beqnat Ir (Aco n))) corps_carre.
(** Nouveau : on peut jouer avec des programmes qui bouclent *)
Definition Pcarre_inf := While Btrue corps_carre.

Inductive SN1_Seq i1 i2 s s2 : Prop :=
| SN1_Seq_intro : forall s1,
    SN i1 s s1 -> SN i2 s1 s2 -> SN1_Seq i1 i2 s s2
.

Inductive SN1_trivial (s s1 : state) : Prop := Triv : SN1_trivial s s1.

Definition dispatch (i: winstr) : state -> state -> Prop :=
  match i with
  | Seq i1 i2 => SN1_Seq i1 i2
  | _ => SN1_trivial
  end.

Definition SN_inv {i s s2} (sn : SN i s s2) : dispatch i s s2 :=
  match sn with
  | SN_Seq i1 i2 s s1 s2 sn1 sn2 =>
    SN1_Seq_intro _ _ _ _ s1 sn1 sn2
  | _ => Triv _ _
  end.

Lemma inv_Seq : forall {i1 i2 s s2}, SN (Seq i1 i2) s s2 -> SN1_Seq i1 i2 s s2.
Proof.
  intros * sn. apply (SN_inv sn).
Qed.


(* 2.3.1 *)

Theorem reduction_Pcarre_2 : SN (Pcarre_2) [0;0;1] [2;4;5].
Proof.
     cbv [Pcarre_2].
  eapply SN_While_true.
  { cbn. reflexivity. }
  { cbv [corps_carre]. eapply SN_Seq. { cbv [incrI]. eapply SN_Assign. } cbn. eapply SN_Seq. cbv [incrX]. eapply SN_Assign. cbn. cbv [incrY]. eapply SN_Assign. }
  cbn. eapply SN_While_true.
  { cbn. reflexivity. }
  { cbv [corps_carre]. eapply SN_Seq. cbv [incrI]. eapply SN_Assign. cbn. eapply SN_Seq. cbv [incrX].
    eapply SN_Assign. cbn. cbv [incrY]. eapply SN_Assign. }
  eapply SN_While_false. { cbn. reflexivity. }
Qed.

(* 2.3.2 *)

Lemma SN_SN' : forall i s s1, SN i s s1 -> SN' i s s1.
Proof.
  intros i s s1 sn.
  induction sn as  [ (* SN_Skip *) s
                   | (* SN_Assign *) x s a
                   | (* SN_Seq *) i1 i2 s1 s2 s' sn1 hrec_sn1 sn2 hrec_sn2
                   | (* SN_If_true *) cond i1 i2 s s' e sn hrec_sn
                   | (* SN_If_false *) cond i1 i2 s s' e sn hrec_sn
                   | (* SN_Ihile_false *) cond i1 s e
                   | (* SN_Ihile_true *)  cond i s s1 s2 e sn1 hrec_sn1 sn2 hrec_sn2
                   ].
  - apply SN'_Skip.
  - apply SN'_Assign.
  - eapply SN'_Seq.
    + apply hrec_sn1.
    + apply hrec_sn2.
  - apply SN'_If_true.
    + apply e.
    + apply hrec_sn.
  - apply SN'_If_false.
    + apply e.
    + apply hrec_sn.
  - apply SN'_While_false. apply e.
  - (** Le sous-but le plus intéressant, où les formulations diffèrent entre
        SN' et SN *)
    apply SN'_While_true.
    + apply e.
    + eapply SN'_Seq.
      -- apply hrec_sn1.
      -- apply hrec_sn2.
Qed.

(* 2.3.3 *)

Lemma SN'_SN : forall i s s1, SN' i s s1 -> SN i s s1.
Proof.
  intros i s s1 sn'.
  induction sn' as [ (* SN_Skip *) s
                   | (* SN_Assign *) x s a
                   | (* SN_Seq *) i1 i2 s1 s2 s' sn1 hrec_sn1 sn2 hrec_sn2
                   | (* SN_If_true *) cond i1 i2 s s' e sn hrec_sn
                   | (* SN_If_false *) cond i1 i2 s s' e sn hrec_sn
                   | (* SN_While_false *) cond i s e
                   | (* SN_While_true *)
                     cond i s0 s2 e sn hrec_sn
                   ].
  - apply SN_Skip.
  - apply SN_Assign.
  - eapply SN_Seq.
    + apply hrec_sn1.
    + apply hrec_sn2.
  - apply SN_If_true.
    + apply e.
    + apply hrec_sn.
  - apply SN_If_false.
    + apply e.
    + apply hrec_sn.
  - apply SN_While_false. apply e.
  - (** Ici il faut exploiter l'hypothèse
        hrec_sn : SN (Seq i (While cond i)) s0 s2
        On observe que cette hypothèse est de la forme SN (Seq i1 i2) s0 s2
        qui est un cas particulier de SN i s0 s2 ;
        cependant un destruct de hrec_sn oublierait que l'on est
        dans ce cas particulier *)
    destruct hrec_sn as [ | | | | | | ].
    + (** Le but obtenu ici correspond au cas où
          [Seq i (While cond i)] serait en même temps [Skip]
          un cas qui est hors propos. *)
      Undo 1.
    Undo 1.
    (** Cela est résolu en utilisant
        conséquence de hrec_sn indiquée par inv_Seq.
        Voir le mode d'emploi indiqué ci-dessus.
     *)
    destruct (inv_Seq hrec_sn) as [s1 sn1 sn2].
    (** On termine en utilisant ici SN_While_true *)
    + eapply SN_While_true.
      -- apply e.
      -- apply sn1.
      -- apply sn2.
Qed.

(* ----- 2.4 Preuves sur la SOS ----- *)


(** * SOS (Sémantique opérationnelle à petits pas) du langage While *)

(* 
Intermédiaire : il reste un pas
s, (i) -> s', (i')
q, (i;i2) -> s', (i', i2)

Final :
s, (i) -> s'!
s, (i;i2) -> s', (i2)
*)

Inductive config :=
| Inter : winstr -> state -> config
| Final : state -> config.

(* La relation pour un pas de SOS *)

Inductive SOS_1: winstr -> state -> config -> Prop :=
| SOS_Skip     : forall s,
                 SOS_1 Skip s (Final s)

| SOS_Assign   : forall x a s,
                 SOS_1 (Assign x a) s (Final (update s x (evalA a s)))

| SOS_Seqf     : forall i1 i2 s s1,
                 SOS_1 i1 s (Final s1) ->
                 SOS_1 (Seq i1 i2) s (Inter i2 s1)
| SOS_Seqi     : forall i1 i1' i2 s s1,
                 SOS_1 i1 s (Inter i1' s1) ->
                 SOS_1 (Seq i1 i2) s (Inter (Seq i1' i2) s1)

| SOS_If_true  : forall b i1 i2 s,
                 evalB b s = true  ->
                 SOS_1 (If b i1 i2) s (Inter i1 s)
| SOS_If_false : forall b i1 i2 s,
                 evalB b s = false ->
                 SOS_1 (If b i1 i2) s (Inter i2 s)

| SOS_While    : forall b i s,
                 SOS_1 (While b i) s (Inter (If b (Seq i (While b i)) Skip) s)
.

(** Fermeture réflexive-transitive de SOS_1 *)
(** Cette sémantique donne toutes les configurations atteignables
    par un (AST de) programme en partant d'un état initial.
 *)

Inductive SOS : config -> config -> Prop :=
| SOS_stop  : forall c, SOS c c
| SOS_again : forall i1 s1 c2 c3,
              SOS_1 i1 s1 c2 -> SOS c2 c3 ->
              SOS (Inter i1 s1) c3.

(* 2.4.1 *)

Theorem SOS_trans : forall c1 c2 c3, SOS c1 c2 -> SOS c2 c3 -> SOS c1 c3.
Proof.
  intros c1 c2 c3.
  intros c12 c23.
  induction c12 as [ | ].
  - apply c23.
  - eapply SOS_again.
    + apply H.
    + apply IHc12.
      apply c23.
Qed.

(* SOS_seq

SOS_seq est l'implication réciproque de SOS_Seqf.

*)

Fixpoint SOS_seq i1 i2 s1 s2 (so : SOS (Inter i1 s1) (Final s2)) :
  SOS (Inter (Seq i1 i2) s1) (Inter i2 s2).
Proof.
Admitted.

(* 2.4.2 *)

Lemma SOS_Pcarre_2_1er_tour : SOS (Inter Pcarre_2 [0;0;1]) (Inter Pcarre_2 [1; 1; 3]).
Proof.
  eapply SOS_again. cbv[Pcarre_2].
  { apply SOS_While. }
  eapply SOS_again.
  Compute(evalB(Bnot (Beqnat Ir (Aco 2))) [0;0;1]).
  { apply SOS_If_true. cbn. reflexivity. }
  eapply SOS_again.
  { cbv. apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign.}
  eapply SOS_again.
  { cbv. apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign.}
  eapply SOS_again.
  { cbv. apply SOS_Seqf. apply SOS_Assign.}
  cbn. cbv[Pcarre_2]. cbv[corps_carre].
  eapply SOS_stop.
Qed.

(* SOS_Pcarre_inf_1er_tour

On montre qu'en partant de l'état i=0, x=0, y=1, on fait un tour de la boucle while et on arrive à l'état i=1, x=1, y=3.

*)

Theorem SOS_Pcarre_inf_1er_tour : SOS (Inter Pcarre_inf [0;0;1]) (Inter Pcarre_inf [1; 1; 3]).
Proof.
  eapply SOS_again.
  { eapply SOS_While.}
  eapply SOS_again.
  { apply SOS_If_true. cbn. reflexivity. }
  eapply SOS_again.
  { apply SOS_Seqi. cbv[corps_carre].
    eapply SOS_Seqf.
    apply SOS_Assign. }
  cbn.
  eapply SOS_again.
  { apply SOS_Seqi.
    apply SOS_Seqf.
    apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqf. 
    apply SOS_Assign. }
  cbn.
  cbv [Pcarre_2].
  apply SOS_stop.
Qed.

(* SOS_Pcarre_2_2e_tour

On montre qu'en partant de l'état i=1, x=1, y=3, on fait un tour de la boucle while et on arrive à l'état i=2, x=4, y=5.
Ce tour est le deuxième tour de boucle.
On rappelle que le premier tour de boucle nous a fait passer de l'état i=0, x=0, y=1 à l'état i=1, x=1, y=3.

*)

Lemma SOS_Pcarre_2_2e_tour : SOS (Inter Pcarre_2 [1; 1; 3]) (Inter Pcarre_2 [2; 4; 5]).
Proof.
Admitted.

(* SOS_Pcarre_2_fini

On veut montrer qu'en partant de l'état i=2, x=4, y=5, on va atteindre l'état i=2, x=4, y=5, c'est-à-dire qu'on veut montrer que notre boucle while se termine.
Ici, on évalue le while et le if, le if est false donc la boucle se termine.

*)


Theorem SOS_Pcarre_2_fini : SOS (Inter Pcarre_2 [2; 4; 5]) (Final [2; 4; 5]).
Proof.
  eapply SOS_again.
  apply SOS_While.
  eapply SOS_again.
  apply SOS_If_false. cbn. reflexivity.
  eapply SOS_again.
  apply SOS_Skip.
  apply SOS_stop.
Qed.


Theorem SOS_Pcarre_2_fin_V1 : SOS (Inter Pcarre_2 [0;0;1]) (Final [2;4;5]).
Proof.
  apply SOS_trans with (Inter Pcarre_2 [1; 1; 3]).
  - apply SOS_Pcarre_2_1er_tour.
  - apply SOS_trans with (Inter Pcarre_2 [2; 4; 5]).
    + apply SOS_Pcarre_2_2e_tour.
    + apply SOS_Pcarre_2_fini.
Qed.

(* 2.4.3 *)

(** Généralisation à Pcarre *)

(** On a besoin de deux lemmes arithmétiques, démontrables avec la tactique ring. *)
Lemma Sn_2 n : S n + S n = S (S (n + n)).
Proof. ring. Qed.

Lemma Sn_carre n : S n * S n = S (n + n + n * n).
Proof. ring. Qed.

Definition invar_cc n := [n; n*n; S (n+n)].

Lemma eqnatb_refl : forall n, eqnatb n n = true.
Proof.
Admitted.

(* SOS_corps_carre 

On veut montrer que lorsqu'on fait un tour de boucle avec comme état initial [n; n*n; S (n+n)], on arrivera à l'état final [S(n); S(n*n); S(n+n)] = [n+1; n*n + S(n+n); S(n+n) + 2]

 *)

Theorem SOS_corps_carre n : SOS (Inter corps_carre (invar_cc n)) (Final (invar_cc (S n))).
Proof.
  eapply SOS_again.
  - cbv [corps_carre].
    + apply SOS_Seqf. apply SOS_Assign.
  - eapply SOS_again.
    + apply SOS_Seqf. apply SOS_Assign.
    + eapply SOS_again.
      apply SOS_Assign. cbn.
      cbv [invar_cc].
      rewrite Sn_carre. rewrite Sn_2.
      apply SOS_stop.
Qed.

(* SOS_corps_carre_inter

On veut montrer que lorsque l'on fait un tour de boucle à une configuration intermédiaire corps_carre; i, SOS sera appliqué seulement à corps_carre et nous arriverons dans une configuration intermédiaire où il nous restera i à exécuter.

 *)

Lemma SOS_corps_carre_inter n i :
  SOS (Inter (Seq corps_carre i) (invar_cc n)) (Inter i (invar_cc (S n))).
Proof.
  apply SOS_seq.
  apply SOS_corps_carre.
Qed.


(* SOS_Pcarre_tour

Pour tout i et n deux entiers,
Si i<>n, alors en appliquant SOS à la configuration intermédiaire ayant comme état invar_cc i, on arrivera à une configuration intermédiaire ayant comme état invar_cc (S i).
On cherche à atteindre l'état i+1 à partir de l'état i pour tout i<>n.

 *)

Lemma SOS_Pcarre_tour :
  forall n i, eqnatb i n = false ->
  SOS (Inter (Pcarre n) (invar_cc i)) (Inter (Pcarre n) (invar_cc (S i))).
Proof.
  intros n i.
  intro eq.
  eapply SOS_again.
  cbv [Pcarre].
  apply SOS_While.
  eapply SOS_again.
  apply SOS_If_true.
  cbn.
  rewrite eq.
  cbn. reflexivity.
  apply SOS_corps_carre_inter.
Qed.

(* SOS_Pcarre_n_fini

On veut montrer qu'en effectuant n tours de boucle depuis une configuration intermédiaire depuis l'état invar_cc n, on arrivera à une configuration finale d'état invar_cc n.
Nous cherchons ici à atteindre un état final et donc à terminer l'éxécution.

 *)

Theorem SOS_Pcarre_n_fini :
  forall n, SOS (Inter (Pcarre n) (invar_cc n)) (Final (invar_cc n)).
Proof.
  intro n.
  eapply SOS_again.
  - cbv [Pcarre].
    apply SOS_While.
  - eapply SOS_again.
    apply SOS_If_false.
    cbn. rewrite eqnatb_refl. cbn. reflexivity.
    eapply SOS_again. apply SOS_Skip.
    apply SOS_stop.
Qed.

(* SOS_Pcarre_2_fin_V2

On veut montrer qu'en partant d'une configuration d'état initial [0;0;1] et en effectuant plusieurs tours de boucle while, on arrivera à une configuration finale d'état [2;4;5].
Ici nous utilisons la transitivité (SOS_trans) afin d'atteindre les différents états puis nous faisons un tour de boucle (SOS_Pcarre_tour) jusqu'à atteindre l'état final.

 *)

Theorem SOS_Pcarre_2_fin_V2 : SOS (Inter Pcarre_2 [0;0;1]) (Final [2;4;5]).
Proof.
  eapply SOS_trans.
  { apply SOS_Pcarre_tour. reflexivity. }
  eapply SOS_trans.
  { apply SOS_Pcarre_tour. reflexivity. }
  eapply SOS_trans.
  { apply SOS_Pcarre_n_fini. }
  apply SOS_stop.
Qed.

(* SOS_Pcarre_inf_tour

Pour tout entier i, 
On veut montrer qu'en bouclant à l'infini la configuration intermédiaire ayant comme état invar_cc i, on arrivera à une configuration intermédiaire ayant comme état invar_cc (S i).
On cherche à atteindre l'état i+1 à partir de l'état i.

*)

Lemma SOS_Pcarre_inf_tour :
  forall i,
  SOS (Inter Pcarre_inf (invar_cc i)) (Inter Pcarre_inf (invar_cc (S i))).
Proof.
  intro i.
  eapply SOS_again.
  cbv [Pcarre_inf].
  apply SOS_While.
  eapply SOS_again.
  apply SOS_If_true.
  cbn. reflexivity.
  apply SOS_corps_carre_inter.
Qed.
  
(* SOS_Pcarre_inf_n

On veut montrer qu'en effectuant un nombre indéfini de tours de boucle depuis une configuration ayant pour état initial [0;0;1], on arrivera à une configuration intermédiaire d'état invar_cc i.

*)

Theorem SOS_Pcarre_inf_n :
  forall i,
  SOS (Inter Pcarre_inf [0; 0; 1]) (Inter Pcarre_inf (invar_cc i)).
Proof.
  intro i.
  induction i as [ | ].
  - cbv [invar_cc]. cbv [Pcarre_inf]. cbn.
    apply SOS_stop.
  - eapply SOS_trans.
    apply IHi.
    eapply SOS_Pcarre_inf_tour.
Qed.

(* 2.4.4 *)

(* Version fonctionnelle de SOS_1 *)

Fixpoint f_SOS_1 (i : winstr) (s : state) : config :=
  match i with
  | Skip => Final s
  | Assign x a => Final (update s x (evalA a s))
  | Seq i1 i2 => match f_SOS_1 i1 s with
                 | Final s1 => Inter i2 s1
                 | Inter i1' s1 => Inter (Seq i1' i2) s1
                 end
  | If b i1 i2 => match evalB b s with
                 | true => Inter i1 s
                 | false => Inter i2 s
                 end
  | While b i => Inter (If b (Seq i (While b i)) Skip) s
  end.

(** ** Utilisation de f_SOS_1 pour éviter les eapply SOS_again *)

(** PC = pt de contrôle *)
Definition PC0 := Pcarre_2.
Eval cbn in (f_SOS_1 PC0 [0;0;1]).

(** Il faut un peu désosser le code pour y retrouver les points de contrôle *)

Definition PC2 := Seq corps_carre PC0.
Definition PC1 := If (Bnot (Beqnat Ir (Aco 2))) PC2 Skip.

(** On vérifie la progression *)
Fact fa1 : f_SOS_1 PC0 [0;0;1] = Inter PC1 [0;0;1]. reflexivity. Qed.
Eval cbn in (f_SOS_1 PC1 [0;0;1]).

Eval cbn in (f_SOS_1 PC2 [0;0;1]).
Definition PC3 := Seq (Seq incrX incrY) PC0.

Eval cbn in (f_SOS_1 PC3 [1;0;1]).
Definition PC4 := Seq incrY PC0.

Eval cbn in (f_SOS_1 PC4 [1;1;1]).

(* Utilisation de la fonction dans la première question du 2.4.2 *)

Lemma SOS_Pcarre_2_1er_tour_V1 : SOS (Inter Pcarre_2 [0;0;1]) (Inter Pcarre_2 [1; 1; 3]).
Proof.
  change Pcarre_2 with PC0.
  apply SOS_again with (Inter PC1 [0;0;1]).
  { apply SOS_While. }
  apply SOS_again with (Inter PC2 [0;0;1]).
  { apply SOS_If_true. cbn. reflexivity. }
  apply SOS_again with (Inter PC3 [1;0;1]).
  { cbv. apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign. }
  apply SOS_again with (Inter PC4 [1;1;1]).
  { cbv. apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign.}
  apply SOS_again with (Inter PC0 [1;1;3]).
  { cbv. apply SOS_Seqf. apply SOS_Assign.}
  apply SOS_stop.
Qed.
