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
Axiom number: forall (x: symbol), ngeq (left x) (right x).
Definition is_number (x: symbol) := ngeq (left x) (right x).
Notation " x _<_ y" := (ngeq x y)
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
Print leq_n.
Lemma no_leq_Zero_minusOne: leq n0 n_1->False. Proof. intros.
apply leq_def in H; destruct H; apply (leq_n n0 n0); [eauto | apply leq_Zero_Zero]. Qed.


(** * Chapter 4: Bad Numbers *)

(** Numbers: Day 3 *)
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




Definition bad_number(X Y Z: symbol):= (leq X Y /\ leq Y Z /\ ~leq X Z).

Lemma bad_numbers: forall (X Y Z: symbol), bad_number X Y Z ->
 (exists x : symbol, In x (left X) /\ bad_number Y Z x) \/
 (exists z : symbol, In z (right Z) /\ bad_number z X Y).

Proof.
  unfold bad_number.
  intros X Y Z H;
  destruct H; destruct H0;
  apply leq_def in H; destruct H;
  apply leq_def in H0; destruct H0;
  rewrite <- leq_def in H1;
  apply not_and_or in H1;
  destruct H1.
  {
    left.
    rewrite forall_ngeq_l in H1.
    apply not_all_ex_not in H1.
    destruct H1.
    apply imply_to_and in H1.
    destruct H1.
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
    apply not_all_ex_not in H1.
    elim H1.
    intros z.
    intros.
    apply imply_to_and in H4.
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

(** day of creation *)

Fixpoint D (s:symbol) (n:nat): nat := 1 + max n (max (fold_right (D) 0 (left s)) (fold_right (D) 0 (right s))).

Definition Dx (l: list symbol) : nat := fold_right (D) 0 l.

Lemma D_eq: forall (X: symbol) (n :nat), D X n = (S( max n ( max (Dx (left X)) (Dx (right X))))).
Proof.
intros; induction X; induction l; induction l0; induction n; unfold left; unfold right; simpl; tauto.
Qed.

Lemma D_ineq: forall (X: symbol) (n :nat), D X n >= D X 0.
Proof.
intros; induction n; repeat rewrite D_eq; lia.
Qed.

Lemma left_g: forall (X x: symbol), In x (left X) -> D X 0 > D x 0.
Proof.
intros; induction X; induction l; elim H; intros.
rewrite H0; rewrite D_eq; simpl; elim D_ineq; intros; lia.
apply IHl in H0; rewrite D_eq; simpl; rewrite D_eq; rewrite D_eq in H0; simpl in H0; lia.
Qed.

Lemma right_g: forall (X x: symbol), In x (right X) -> D X 0 > D x 0.
Proof.
intros; induction X; induction l0; elim H; intros.
rewrite H0; rewrite D_eq; simpl; elim D_ineq; intros; lia.
apply IHl0 in H0; rewrite D_eq; simpl; rewrite D_eq; rewrite D_eq in H0; simpl in H0; lia.
Qed.


Lemma bad_numbers_dec: forall (X Y Z: symbol) (n :nat), bad_number X Y Z -> D X 0 + D Y 0 + D Z 0 = n ->
 ((exists x : symbol, In x (left X) /\ bad_number Y Z x /\ D x 0 + D Y 0 + D Z 0 < n ) \/
 ((exists z : symbol, In z (right Z) /\ bad_number z X Y /\ D X 0 + D Y 0 + D z 0 < n))).
Proof.
intros; apply bad_numbers in H.
repeat destruct H.
left; exists x; split; eauto; split; eauto; apply left_g in H; lia.
right; exists x; split; eauto; split; eauto; apply right_g in H; lia.
Qed.


Lemma bad_numbers_do_not_exists: forall (n: nat) (X Y Z: symbol), bad_number X Y Z -> D X 0 + D Y 0 + D Z 0 < n -> False. 
Proof.
intro; induction n; lia || auto; intros; apply (bad_numbers_dec X Y Z (D X 0 + D Y 0 + D Z 0)) in H; auto; 
repeat destruct H; destruct H1; [apply (IHn Y Z x ) | apply (IHn x X Y) ]; lia||auto.
Qed.

(** leq transitivity *)
Lemma T1: forall (X Y Z: symbol), leq X Y -> leq Y Z -> leq X Z.
Proof.
intros; elim (classic (X _<=_ Z)); eauto; intros; cut (False); tauto || auto.
apply (bad_numbers_do_not_exists ( S (D X 0 + D Y 0 + D Z 0)) X Y Z); [ unfold bad_number| ]; auto.
Qed.

(** * Chapter 5: Progress *)

Lemma bad_numbers_leq_dec: forall (X Y: symbol), (leq X Y -> False) -> 
((exists x: symbol, In x (left X) /\ leq Y x) \/
 (exists y: symbol, In y (right Y) /\ leq y X)).
Proof.
intros; rewrite <- leq_def in H;apply not_and_or in H;
destruct H; [ rewrite forall_ngeq_l in H | rewrite forall_ngeq_r in H];
apply not_all_ex_not in H;
destruct H;
apply imply_to_and in H;
destruct H;
[ left | right ];
exists x;
split; 
[ | rewrite <- (ngeq_n Y x) in H0 | | rewrite <- (ngeq_n x X) in H0 ];
eauto.
Qed.

Lemma pre_T3: forall (n: nat) (X: symbol), D X 0 < n -> leq X X.
Proof.
intro n;induction n.
intros;lia.
intros X H; pose proof (number X).
rewrite <- leq_def;split;
[rewrite forall_ngeq_l | rewrite forall_ngeq_r];
intros x H1; rewrite leq_n; intros H2;
cut (D x 0 < n); [ |apply left_g in H1;lia | |apply right_g in H1;lia ];
intros H3; rewrite <- leq_def in H2; destruct H2; pose proof H1;
[rewrite forall_ngeq_l in H2; apply (H2 x) in H1 | rewrite forall_ngeq_r in H4; apply (H4 x) in H1 ];
rewrite leq_n in H1; apply H1; apply (IHn x); auto.
Qed.

Lemma T3: forall (X: symbol), leq X X.
Proof.
intro; apply (pre_T3 (S (D X 0))); auto.
Qed.

Lemma pre_T2_l: forall (n: nat) (X: symbol), D X 0 < n -> forall (xl: symbol), In xl (left X) -> leq xl X.
Proof.
intros n; induction n.
lia.
intros X N xl.
pose proof (number X).
intros H0; apply leq_def; split.
2:{ unfold is_number in H; induction (left X); elim H0; rewrite forall_ngeq_l in H; eauto.
  }
1:{
 elim (classic ( ngeq (left xl) [X])); eauto; intros; cut (False); tauto || auto;
 rewrite forall_ngeq_l in H1; apply not_all_ex_not in H1; destruct H1 as [xll];
 destruct H1; intros; rewrite leq_n; intros;
 cut (xll _<=_ xl).
 2:{ apply IHn; [apply left_g in H0; lia| auto].
    }
 1:{ intros; 
     cut (X _<=_ xl). 2:{ apply (T1 X xll xl);auto. }
     pose proof (number xl).
     intros; rewrite <- leq_def in H5; destruct H5; rewrite forall_ngeq_l in H5;
     apply (H5 xl) in H0; rewrite leq_n in H0; apply H0;apply (T3 xl); auto.
   }
}
Qed.

Lemma T2_l: forall (X xl: symbol), In xl (left X) -> leq xl X.
Proof.
intros X xl.
apply (pre_T2_l (S (D X 0))); auto.
Qed.

Lemma pre_T2_r: forall (n: nat) (X: symbol), D X 0 < n -> forall (xr: symbol), In xr (right X) -> leq X xr.
Proof.
intros n; induction n.
lia.
intros X N xr.
pose proof (number X).
intros H0; apply leq_def; split.
unfold is_number in H; induction (right X); [elim H0| rewrite forall_ngeq_r in H; auto].

elim (classic ( ngeq [X] (right xr))); eauto; intros; cut (False); tauto || auto.
 rewrite forall_ngeq_r in H1; apply not_all_ex_not in H1; destruct H1 as [xrr].
 destruct H1; intros; rewrite leq_n; intros;
 cut (xr _<=_ xrr).
 2:{ apply IHn; [ apply right_g in H0;lia | auto].
    }
 1:{ intros; 
     cut (xr _<=_ X). 2:{ apply (T1 xr xrr X);auto. }
     pose proof (number xr).
     intros. rewrite <- leq_def in H5. destruct H5; rewrite forall_ngeq_r in H6;
     apply (H6 xr) in H0; rewrite leq_n in H0; apply H0; apply (T3 xr); auto.
   }
Qed.

Lemma T2_r: forall (X xr: symbol), In xr (right X) -> leq X xr.
Proof.
intros X xr.
apply (pre_T2_r (S (D X 0))); auto.
Qed.

Lemma T4: 
forall (X Y: symbol), (leq X Y -> False) -> leq Y X.
Proof.
intros.
intros; elim (classic (leq Y X)); eauto; intros; cut (False); tauto || auto.
destruct (bad_numbers_leq_dec X Y);eauto.
repeat destruct H1.
apply (T2_l X x) in H1. 
apply (T1 Y x X) in H2; tauto.
repeat destruct H1.
apply (T2_r Y x) in H1.
apply (T1 Y x X) in H2; tauto.
Qed.

Lemma T5: 
forall (X Y Z: symbol), ngeq [X] [Y] -> leq Y Z ->  ngeq [X] [Z].
Proof.
intros; rewrite leq_n; rewrite leq_n in H; intros; elim H; apply (T1 Y Z X); auto.
Qed.

Lemma T6: 
forall (X Y Z: symbol), leq X Y -> ngeq [Y] [Z] ->  ngeq [X] [Z].
Proof.
intros; rewrite leq_n; rewrite leq_n in H0; intros; elim H0; apply (T1 Z X Y); auto.
Qed.

(** * Chapter 6: The third day *)

Lemma ngeq_const_l: forall (X Y: list symbol) (x: symbol), ngeq X Y /\ ngeq [x] Y <-> ngeq (x::X) Y.
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

Lemma ngeq_const_r: forall (X Y: list symbol) (y: symbol), ngeq X Y /\ ngeq X [y] <-> ngeq X (y::Y).
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

Lemma ngeq_concat_l: forall (X1 X2 Z: list symbol), ngeq X1 Z /\ ngeq X2 Z <-> ngeq (X1++X2) Z.
Proof.
split.
induction X1;intros;repeat destruct H;auto.
rewrite <- ngeq_const_l in H; repeat destruct H; simpl; rewrite <- ngeq_const_l; auto.

induction X1.
simpl; intros; rewrite forall_ngeq_l; simpl; tauto.
simpl; intros; rewrite <- ngeq_const_l in H; repeat destruct H; rewrite <- ngeq_const_l; tauto.
Qed.

Lemma ngeq_concat_r: forall (X1 X2 Z: list symbol), ngeq Z X1 /\ ngeq Z X2 <-> ngeq Z (X1++X2).
Proof.
split.
induction X1;intros;repeat destruct H;auto.
rewrite <- ngeq_const_r in H; repeat destruct H; simpl; rewrite <- ngeq_const_r; auto.

induction X1.
simpl; intros; rewrite forall_ngeq_r; simpl; tauto.
simpl; intros; rewrite <- ngeq_const_r in H; repeat destruct H; rewrite <- ngeq_const_r; tauto.
Qed.


Definition eqq (X Y: symbol) : Prop := leq X Y /\ leq Y X .

Lemma T7: 
forall (X Y:symbol),  ngeq (left Y) [X] -> ngeq [X] (right Y) -> eqq X (pair (left X ++ left Y) (right X ++ right Y)).
Proof.
intros.
pose proof (T3 X) as P; apply leq_def in P; destruct P as [P1 P2].
pose proof (T3 (pair (left X ++ (left Y)) (right X ++ (right Y)))) as Q; apply leq_def in Q; destruct Q as [Q1 Q2]; simpl in Q1, Q2.
split; rewrite <- leq_def; simpl; split;
[ rewrite <- ngeq_concat_l in Q1 
| rewrite <- ngeq_concat_r 
| rewrite <- ngeq_concat_l 
| rewrite <- ngeq_concat_r in Q2
]; tauto.
Qed.
