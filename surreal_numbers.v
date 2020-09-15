Require Import List.
Import ListNotations.
Require Import Classical.
Require Import Classical_Prop.
Require Import Arith.
Require Import Arith.Max.
Require Import Coq.micromega.Lia.
Require Import Coq.Structures.GenericMinMax.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Equality.

(** * Chapter 1: The Rock
----
In the beginning, everything was void, and J. H. W. H. Conway began to create numbers. Conway said,

"Let there be two rules which bring forth all numbers large and small. 
This shall be the first rule: Every number corresponds to two sets of previously 
created numbers, such that no member of the left set is greater than or equal to any 
member of the right set. And the second rule shall be this: One number is less than or 
equal to another number if and only if no member of the first number's left set is greater 
than or equal to the second number, and no member of the second number's right 
set is less than or equal to the first number." 

And Conway examined these two rules he had made, and behold! They were very good.
And the first number was created from the void left set and the void right set.
Conway called this number "zero," and said that it shall be a sign to separate 
positive numbers from negative numbers. Conway proved that zero was less than 
or equal to zero, and he saw that it was good. And the evening and the morning 
were the day of zero. On the next day, two more numbers were created, one
with zero as its left set and one with zero as its right set. And Conway called 
the former number "one," and the latter he called "minus one." And he proved 
that minus one is less than but not equal to zero and zero is less than but not 
equal to one. And the evening
*)



(** * Chapter 2: Symbols *)



(** Symbols definition: *)

Inductive symbol: Type :=
| pair: list symbol -> list symbol -> symbol.
Notation "( x , y )" := (pair x y).

Definition left (s : symbol) : list symbol :=
match s with
| pair l _ => l
end.

Definition right (s : symbol) : list symbol :=
match s with
| pair _ r => r
end.


(** Rule 1 *)
Axiom ngeq: list symbol-> list symbol -> Prop.
Definition is_number (x: symbol) := ngeq (left x) (right x).
Notation "~ ( x _>=_ y )" := (ngeq x y)
 (at level 60, right associativity).
Axiom forall_ngeq_r: forall (X Y: list symbol), ngeq X Y <-> forall (y: symbol), In y Y -> ngeq X [y].
Axiom forall_ngeq_l: forall (X Y: list symbol), ngeq X Y <-> forall (x: symbol), In x X -> ngeq [x] Y.


(** Rule 2 *)
Axiom leq: symbol-> symbol -> Prop.
Axiom leq_def: forall (X: symbol), forall (Y: symbol), (ngeq (left X) [Y] /\ ngeq [X] (right Y)) <-> leq X Y.
Notation "x _<=_ y" := (leq x y)
 (at level 60, right associativity).

(** Numbers: Day 1 *)

Definition n0 := ([],[]).

Lemma Zero_is_number: (is_number n0). Proof. apply forall_ngeq_l; intros; tauto. Qed.



(** Numbers: Day 2 *)
Definition n_1 := ([],[n0]).
Definition n1 := ([n0],[]).

(** * Chapter 3: Proofs *)

Lemma One_is_number: (is_number n1). Proof. apply forall_ngeq_r; intros; tauto. Qed.
Lemma minusOne_is_number: (is_number n_1). Proof. apply forall_ngeq_l; intros; tauto. Qed.
Lemma leq_Zero_Zero: leq n0 n0. Proof. apply leq_def; split; [apply forall_ngeq_l | apply forall_ngeq_r]; intros; tauto. Qed.
Lemma leq_minusOne_Zero: leq n_1 n0. Proof. apply leq_def; split; [apply forall_ngeq_l | apply forall_ngeq_r]; intros; tauto. Qed.
Lemma leq_Zero_minusOne: (leq n0 n1). Proof. apply leq_def; split; [apply forall_ngeq_l | apply forall_ngeq_r]; intros; tauto. Qed.
Lemma leq_minusOne_One: leq n_1 n1. Proof. apply leq_def. split; [apply forall_ngeq_l | apply forall_ngeq_r]; intros; tauto. Qed.

Axiom leq_n: forall (X: symbol), forall (Y: symbol), ngeq [Y] [X] <-> (leq X Y -> False).
Axiom ngeq_n: forall (X: symbol), forall (Y: symbol), leq X Y <-> (ngeq [Y] [X] -> False).

Lemma no_leq_Zero_minusOne: leq n0 n_1->False. Proof. intros.
apply leq_def in H; destruct H; apply (leq_n n0 n0); [eauto | apply leq_Zero_Zero]. Qed.


(** * Chapter 4: Bad Numbers *)

(* Dia N *)
Definition na := ([n_1],[]).
Definition nb := ([n0],[]).
Definition nc := ([n1],[]).

Definition nd := (n_1::[n0],[]).
Definition ne := (n_1::[n1],[]).
Definition nf := (n0::[n1],[]).
Definition ng := (n_1::n0::[n1],[]).

Lemma is_num_abcdefg: is_number(na) /\ is_number(nb) /\ is_number(nc) /\ is_number(nd) /\ is_number(ne) /\ is_number(nf) /\ is_number(ng).
Proof. 
repeat split; apply forall_ngeq_r; intros; tauto.
Qed.

Definition nh := ([], [n_1]).
Definition ni := ([], [n0]).
Definition nj := ([], [n1]).

Definition nk := ([], n_1::[n0]).
Definition nl := ([], n_1::[n1]).
Definition nm := ([], n0::[n1]).
Definition nn := ([], n_1::n0::[n1]).

Lemma nums_hijklmn: is_number(nh) /\ is_number(ni) /\ is_number(nj) /\ is_number(nk) /\ is_number(nl) /\ is_number(nm) /\ is_number(nn).
Proof. 
repeat split; apply forall_ngeq_l; intros; tauto.
Qed.

Definition no := ([n_1], [n0]).
Definition np := ([n0],[n1]).
Definition nq := ([n_1],[n1]).


Lemma nums_opq: is_number(no) /\ is_number(np) /\ is_number(nq).
Proof.
repeat split; apply forall_ngeq_r; intros.
{
 elim H; intros; 
 [rewrite <- H0; apply leq_n; intros; apply leq_def in H1; destruct H1; apply leq_n in H2; [tauto | apply leq_Zero_Zero]
 | intros; tauto ].
}
{
 elim H; intros; 
 [rewrite <- H0; apply leq_n; intros; apply leq_def in H1; destruct H1; apply leq_n in H1; [tauto | apply leq_Zero_Zero ]
 | intros; tauto ].
}
{
 elim H; intros; 
 [rewrite <- H0; apply leq_n; intros; apply leq_def in H1; destruct H1; apply leq_n in H1; [tauto | apply leq_minusOne_Zero]
 | intros; tauto ].
}
Qed.

Definition nr := (n_1::[n0], [n1]).
Definition ns := ([n_1], n0::[n1]).

Lemma nums_rs: is_number(nr) /\ is_number(ns).
Proof.
split; [apply forall_ngeq_l | apply forall_ngeq_r]; intros.
{
 destruct H; 
 [ rewrite <-H; apply leq_n; intros; apply leq_def in H0; destruct H0; apply leq_n in H0; [ tauto | apply leq_minusOne_Zero]
 | destruct H; [ rewrite <-H; apply leq_n; intros; apply leq_def in H0; destruct H0; apply leq_n in H0; [ tauto | apply leq_Zero_Zero ] | tauto] ].
}
{
 destruct H; 
 [ rewrite <-H; apply leq_n; intros; apply leq_def in H0; destruct H0; apply leq_n in H1; [ tauto | apply leq_Zero_Zero ]
 | destruct H; [ rewrite <-H; apply leq_n; intros; apply leq_def in H0; destruct H0; apply leq_n in H0; [ tauto | apply leq_minusOne_Zero ] | tauto]].
}
Qed.

(*
Lemma ngeq_l: forall (X Y: list symbol) (x: symbol), ngeq X Y /\ ngeq [x] Y <-> ngeq (x::X) Y.
Proof.
split.
{ 
intros; destruct H; apply forall_ngeq_l; intros; elim H1.
intros; rewrite <-H2; tauto.
apply forall_ngeq_l; tauto.
} {
intros; rewrite (forall_ngeq_l (x :: X) Y) in H; split.
rewrite (forall_ngeq_l X Y); intros; apply H; apply in_cons; eauto.
apply H; apply in_eq.
}
Qed.

Lemma ngeq_r: forall (X Y: list symbol) (y: symbol), ngeq X Y /\ ngeq X [y] <-> ngeq X (y::Y).
Proof.
split.
{ 
intros; destruct H; apply forall_ngeq_r; intros; elim H1.
intros; rewrite <-H2; tauto.
apply forall_ngeq_r; tauto.
} {
intros; rewrite (forall_ngeq_r X (y :: Y)) in H; split.
rewrite (forall_ngeq_r X Y); intros; apply H; apply in_cons; eauto.
apply H; apply in_eq.
}
Qed.
*)


(* ----------------- Lemas auxiliares -----------------*)
Lemma not_leq_to_or: forall (X Y: symbol), (leq X Y -> False) -> ((ngeq (left X) [Y]-> False) \/ (ngeq [X] (right Y) ->False)).
Proof.
intros.
elim (classic ((ngeq (left X) [Y] /\ ngeq [X] (right Y)))) ; [ intros ; apply leq_def in H0 |] ; tauto.
Qed.

Lemma not_forall_exists_not_l: forall (x Y: symbol),forall (X: list symbol),
 ((~ forall x : symbol, In x X -> ngeq [x] [Y])) ->
 ((exists x : symbol, In x X /\ (ngeq [x] [Y]->False))).
Proof.
intros.
apply not_all_ex_not in H.
unfold not in H.
elim H.
intros.
exists x0.
tauto.
Qed.

Lemma not_forall_exists_not_r: forall (y X: symbol),forall (Y: list symbol),
 ((~ forall y : symbol, In y Y -> ngeq [X] [y])) ->
 ((exists y : symbol, In y Y /\ (ngeq [X] [y]->False))).
Proof.
intros.
apply not_all_ex_not in H.
unfold not in H.
elim H.
intros.
exists x.
tauto.
Qed.


Definition bad_number(X Y Z: symbol):= (leq X Y /\ leq Y Z /\ ~leq X Z).

(* ----------------- Lemas auxiliares -----------------*)

Lemma bad_numbers: forall (X Y Z: symbol), bad_number X Y Z ->
 (exists x : symbol, In x (left X) /\ bad_number Y Z x) \/
 (exists z : symbol, In z (right Z) /\ bad_number z X Y).

Proof.
  unfold bad_number.
  intros X Y Z H;
  destruct H; destruct H0;
  apply leq_def in H; destruct H;
  apply leq_def in H0; destruct H0;
  apply not_leq_to_or in H1; destruct H1.
  {
    left.
    rewrite forall_ngeq_l in H1.
    apply not_forall_exists_not_l in H1 ; auto.
    repeat destruct H1.
    exists x.
    split.
    tauto.
    split. { apply leq_def. split;  eauto. }
           { split. { apply ngeq_n. eauto. }
                    { unfold not. apply leq_n. rewrite (forall_ngeq_l (left X) [Y]) in H. eauto. } }
  }
  {
    right.
    rewrite forall_ngeq_r in H1.
    apply not_forall_exists_not_r in H1 ; auto.
    elim H1.
    intros z.
    intros.
    destruct H4.
    exists z.
    split.
    tauto.
    split. 
     {apply ngeq_n. eauto. }
            { split; [ apply leq_def | unfold not; apply leq_n; rewrite (forall_ngeq_r [Y] (right Z)) in H3]; eauto. } 
  }
Qed.

(**Mas numeros **)

Fixpoint D (s:symbol) (n:nat): nat := 1 + max n (max (fold_right (D) 0 (left s)) (fold_right (D) 0 (right s))).

Definition Dx (l: list symbol) : nat := fold_right (D) 0 l.


Lemma one_number_lower_limit: forall (X: symbol)(n :nat), D X n >=1.
Proof.
induction X; induction l; induction l0; induction n; simpl; lia.
Qed.

Lemma three_numbers_lower_limit: forall (X Y Z: symbol), D X 0 + D Y 0 + D Z 0 >=3.
Proof.
intros.
elim (one_number_lower_limit X); [elim (one_number_lower_limit Y); [elim (one_number_lower_limit Z) | ] | ]; lia.
Qed.


Lemma aux: forall (X: symbol) (n :nat), D X n = max (S n) (D X 0).
Proof.
intros; induction X; induction l; induction l0; simpl; lia.
Qed.

Lemma aux3: forall (X: symbol), D X 0 = max (S(Dx (left X))) (S(Dx (right X))).
Proof.
intros; induction X; induction l; induction l0; tauto.
Qed.

Lemma aux4: forall (X: symbol) (n :nat), D X n = ( max (S(n)) ((( max (S(Dx (left X))) (S(Dx (right X))))))).
Proof.
intros; induction X; induction l; induction l0; induction n; unfold left; unfold right; simpl; tauto.
Qed.

Lemma aux5: forall (X: symbol) (n :nat), D X n >= D X 0.
Proof.
intros; induction n.
elim one_number_lower_limit; auto.
rewrite aux4; rewrite aux3; lia.
Qed.

Lemma aux6: forall (X: symbol) (n :nat), (D X n) = (S( max n ( max (Dx (left X)) (Dx (right X))))).
Proof.
intros; induction X; induction l; induction l0; induction n; unfold left; unfold right; simpl; tauto.
Qed.

Lemma auxn_l: forall (X x: symbol), In x (left X) -> D X 0 > D x 0.
Proof.
intros; induction X; unfold left in H.
induction l; elim H; intros.
rewrite H0; rewrite aux4; unfold left; simpl; elim aux5; intros; lia.
apply IHl in H0; rewrite aux6; unfold right; unfold left; simpl; rewrite aux; rewrite aux6 in H0; simpl in H0; lia.
Qed.

Lemma auxn_r: forall (X x: symbol), In x (right X) -> D X 0 > D x 0.
Proof.
intros; induction X; unfold right in H.
induction l0; elim H; intros.
rewrite H0; rewrite aux4; unfold left; simpl; elim aux5; intros; lia.
apply IHl0 in H0; rewrite aux6; unfold right; unfold left; simpl; rewrite aux; rewrite aux6 in H0; simpl in H0; lia.
Qed.


Lemma bad_numbers_dec: forall (X Y Z: symbol) (n :nat), bad_number X Y Z -> D X 0 + D Y 0 + D Z 0 = n ->
 ((exists x : symbol, In x (left X) /\ bad_number Y Z x /\ D x 0 + D Y 0 + D Z 0 < n ) \/
 ((exists z : symbol, In z (right Z) /\ bad_number z X Y /\ D X 0 + D Y 0 + D z 0 < n))).
Proof.
intros; apply bad_numbers in H.
repeat destruct H.
left; exists x; split; eauto; split; eauto; apply auxn_l in H; lia.
right; exists x; split; eauto; split; eauto; apply auxn_r in H; lia.
Qed.


Lemma ex_leq_trans: 
forall (n: nat) (X Y Z: symbol), bad_number X Y Z -> D X 0 + D Y 0 + D Z 0 < n -> False. 
Proof.
intro; induction n; lia||auto; intros; apply (bad_numbers_dec X Y Z (D X 0 + D Y 0 + D Z 0)) in H; auto; 
repeat destruct H; destruct H1; [apply (IHn Y Z x ) | apply (IHn x X Y) ]; lia||auto. 
Qed.

Lemma leq_trans: 
forall (X Y Z: symbol), leq X Y -> leq Y Z -> leq X Z.
Proof.
intros.
elim (classic (X _<=_ Z)); eauto.
intros.
cut (False); tauto || auto.
apply (ex_leq_trans ( S (D X 0 + D Y 0 + D Z 0)) X Y Z).
unfold bad_number; auto.
lia.
Qed.

