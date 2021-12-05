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
                   | (* SN_Ihile_false *) cond i1 s hrec_sn
                   | (* SN_Ihile_true *)  cond i1 s hrec_sn
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
  - apply SN'_While_false. apply hrec_sn.
  - (** Le sous-but le plus intéressant, où les formulations diffèrent entre
        SN' et SN *)
    apply SN'_While_true.
    + apply H.
    + eapply SN'_Seq.
      -- apply IHsn1.
      -- apply IHsn2.
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
