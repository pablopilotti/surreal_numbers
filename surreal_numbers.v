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
Require Import Coq.Lists.ListSet.

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
| pair: set symbol -> set symbol -> symbol.
Notation "( x , y )" := (pair x y).

Fixpoint symbol_eq_dec (t1 t2 : symbol) : {t1 = t2} + {t1 <> t2}.
Proof.
  set (symbol_list_eq_dec := list_eq_dec symbol_eq_dec).
  decide equality.
Defined.

Axiom Symbol_Set: forall (s:set symbol), NoDup s.

Definition add := set_add symbol_eq_dec.

Definition union := set_union symbol_eq_dec.

Theorem set_add_new: forall a x,
    ~In a x -> add a x = x++[a].
Proof.
  intros. induction x.
  - simpl. auto.
  - apply not_in_cons in H. inversion H. 
    apply IHx in H1. simpl.
    case (symbol_eq_dec a a0).
    + intros. contradict H0.  auto.
    + rewrite H1. auto.
Qed.

Theorem union_empty: forall (x: set symbol), 
    union [] x  = List.rev x.
Proof.
  intros. pose proof Symbol_Set x as H. induction x.
  - simpl.  auto.
  - rewrite NoDup_cons_iff in H.
    inversion H.  simpl. apply IHx in H1.
    rewrite in_rev in H0.
    apply set_add_new in H0.
    rewrite H1.
    unfold add in H0.
    rewrite H0. auto.
Qed.

Definition left (s : symbol) : set symbol :=
match s with
| pair l _ => l
end.

Definition right (s : symbol) : set symbol :=
match s with
| pair _ r => r
end.

Program Fixpoint nodup_s (s: symbol) : symbol :=
match s with
| pair [] [] => s
| pair l1 l2 => (pair (nodup symbol_eq_dec (map nodup_s l1)) (nodup symbol_eq_dec (map nodup_s l2)))
end.

Lemma nodup_in: forall (a: symbol) (s: list symbol), In a s <-> (nodup symbol_eq_dec (a::s)) = (nodup symbol_eq_dec s).
Proof.
split.
intros; simpl; case (in_dec symbol_eq_dec a s);tauto.
case (in_dec symbol_eq_dec a s); auto; intro; simpl; elim in_dec; auto; intros.
symmetry in H; rewrite <- (hd_error_tl_repr (nodup symbol_eq_dec s) a (nodup symbol_eq_dec s)) in H.
destruct H; induction (nodup symbol_eq_dec s).
apply hd_error_some_nil in H; tauto.
simpl in H0; simpl in H; apply IHl; rewrite H0; auto.
Qed.


Lemma prue2: forall (a: symbol) (s s2: list symbol), In a s -> ~In a s2 -> nodup symbol_eq_dec (s2 ++ (a::s)) = (nodup symbol_eq_dec (s2 ++ s)).
Proof.
intros a s s2 H H2.
induction s2.
apply nodup_in.
auto.
apply not_in_cons in H2.
destruct H2.
simpl.
rewrite (IHs2 H1).
clear IHs2.
elim in_dec; elim in_dec; intros; auto.
apply in_elt_inv in a1.
elim a1. 
{intros. unfold not in H0. elim H0. auto. }
{intros. unfold not in b. elim b. auto. }
cut False. tauto.
clear H H1.
rewrite in_app_iff in a1.
rewrite in_app_iff in b.
simpl in b.
apply not_or_and in b.
destruct b.
apply not_or_and in H1.
destruct H1.
tauto.
Qed.


Lemma in_union_nodup: forall (a: symbol) (s1 s2: list symbol), In a (union (nodup symbol_eq_dec s1) (nodup symbol_eq_dec s2)) <-> In a (nodup symbol_eq_dec (s2 ++ s1)).
Proof.
intros.
rewrite nodup_In.
split.
intros.
apply set_union_elim in H.
rewrite nodup_In in H.
rewrite nodup_In in H.
apply in_app_iff.
tauto.
intros.
apply set_union_intro.
rewrite nodup_In.
rewrite nodup_In.
apply in_app_iff in H.
tauto.
Qed.

(** Rule 1 *)
Axiom ngeq: set symbol-> set symbol -> Prop.
Axiom number: forall (x: symbol), ngeq (left x) (right x).
Definition is_number (x: symbol) := ngeq (left x) (right x).
Notation " x _<_ y" := (ngeq x y)
 (at level 60, right associativity).
Axiom forall_ngeq_r: forall (X Y: set symbol), ngeq X Y <-> forall (y: symbol), In y Y -> ngeq X [y].
Axiom forall_ngeq_l: forall (X Y: set symbol), ngeq X Y <-> forall (x: symbol), In x X -> ngeq [x] Y.


Lemma set_list_l: forall (X Y: set symbol) (x: symbol), ngeq (x::X) Y <-> ngeq (add x X) Y.
Proof.
intros; case X; [tauto | ]; intros a l; simpl; 
case (symbol_eq_dec x a); intros; [rewrite e| ]; repeat rewrite forall_ngeq_l; 
simpl; split; intros; apply H; destruct H0; auto.
apply set_add_elim in H0; destruct H0; [ rewrite H0 | ] ; tauto.
rewrite H0; right; apply set_add_intro; tauto.
destruct H0; [tauto | right; apply set_add_intro; tauto].
Qed.

Lemma set_list_r: forall (Y X: set symbol) (y: symbol), ngeq X (y::Y)  <-> ngeq X (add y Y).
Proof.
intros; case Y; [tauto | ]; intros a l; simpl; 
case (symbol_eq_dec y a); intros; [rewrite e| ]; repeat rewrite forall_ngeq_r; 
simpl; split; intros; apply H; destruct H0; auto.
apply set_add_elim in H0; destruct H0; [ rewrite H0 | ] ; tauto.
rewrite H0; right; apply set_add_intro; tauto.
destruct H0; [tauto | right; apply set_add_intro; tauto].
Qed.

Lemma set_list_l_app: forall (X Y Z: set symbol), ngeq (X ++ Y) Z <-> ngeq (union X Y) Z.
Proof.
intros.
repeat rewrite forall_ngeq_l.
case X;simpl;intros. 
rewrite union_empty; split; intros; apply H; [rewrite <- in_rev in H0 | rewrite in_rev in H0]; auto.
split; intros; apply H.
rewrite (set_union_iff symbol_eq_dec) in H0; repeat destruct H0; try tauto; try right; rewrite in_app_iff; tauto.
rewrite (set_union_iff symbol_eq_dec); rewrite in_app_iff in H0.
repeat destruct H0; [left; apply in_eq | left; apply in_cons; auto | tauto].
Qed.

Lemma app_l_swap: forall (X Y Z: set symbol), ngeq (X ++ Y) Z <-> ngeq (Y ++ X) Z.
Proof.
intros; repeat rewrite forall_ngeq_l; split; intros; apply H; rewrite in_app_iff; rewrite in_app_iff in H0; tauto.
Qed.

Lemma app_r_swap: forall (X Y Z: set symbol), ngeq X (Y ++ Z) <-> ngeq X (Z ++ Y).
Proof.
intros; repeat rewrite forall_ngeq_r; split; intros; apply H; rewrite in_app_iff; rewrite in_app_iff in H0; tauto.
Qed.

Lemma set_list_r_app: forall (X Y Z: set symbol), ngeq X (Y ++ Z) <-> ngeq X (union Y Z).
Proof.
intros.
repeat rewrite forall_ngeq_r.
case Y; simpl; intros.
rewrite union_empty; split; intros; apply H; [rewrite <- in_rev in H0 | rewrite in_rev in H0]; auto.
split; intros; apply H.
rewrite (set_union_iff symbol_eq_dec) in H0; repeat destruct H0; try tauto; try right; rewrite in_app_iff; tauto.
rewrite (set_union_iff symbol_eq_dec); rewrite in_app_iff in H0.
repeat destruct H0; [left; apply in_eq | left; apply in_cons; auto | tauto].
Qed.


Lemma previo: forall (Z X: set symbol), X _<_ Z -> rev X _<_ Z.
Proof.
intros; apply forall_ngeq_l; intros; rewrite <- (in_rev X x) in H0; rewrite forall_ngeq_l in H; auto.
Qed.


(** Rule 2 *)
Axiom leq: symbol-> symbol -> Prop.
Axiom leq_def: forall (X: symbol), forall (Y: symbol), (ngeq (left X) [Y] /\ ngeq [X] (right Y)) <-> leq X Y.
Notation "x _<=_ y" := (leq x y)
 (at level 60, right associativity).

(** Numbers: Day 1 *)

Definition n0 := ([],[]).

Lemma Zero_is_number: (is_number n0). 
Proof. 
apply forall_ngeq_l; intros; tauto. 
Qed.

(** Numbers: Day 2 *)
Definition n_1 := ([],[n0]).
Definition n1 := ([n0],[]).

(** * Chapter 3: Proofs *)

Lemma One_is_number: (is_number n1). 
Proof. 
apply forall_ngeq_r; intros; tauto. 
Qed.

Lemma minusOne_is_number: (is_number n_1).
Proof. 
apply forall_ngeq_l; intros; tauto.
Qed.

Lemma leq_Zero_Zero: leq n0 n0.
Proof. 
apply leq_def; split; [apply forall_ngeq_l | apply forall_ngeq_r]; intros; tauto. 
Qed.

Lemma leq_minusOne_Zero: leq n_1 n0.
Proof.
apply leq_def; split; [apply forall_ngeq_l | apply forall_ngeq_r]; intros; tauto. 
Qed.

Lemma leq_Zero_minusOne: (leq n0 n1).
Proof.
apply leq_def; split; [apply forall_ngeq_l | apply forall_ngeq_r]; intros; tauto.
Qed.

Lemma leq_minusOne_One: leq n_1 n1. 
Proof. 
apply leq_def. split; [apply forall_ngeq_l | apply forall_ngeq_r]; intros; tauto.
Qed.

Axiom leq_n: forall (X: symbol), forall (Y: symbol), ngeq [Y] [X] <-> (leq X Y -> False).
Axiom ngeq_n: forall (X: symbol), forall (Y: symbol), leq X Y <-> (ngeq [Y] [X] -> False).

Lemma no_leq_Zero_minusOne: leq n0 n_1->False. 
Proof.
intros; apply leq_def in H; destruct H; apply (leq_n n0 n0); [eauto | apply leq_Zero_Zero].
Qed. 

(** * Chapter 4: Bad Numbers *)

(** Numbers: Day 3 *)
Definition na := ([n_1],[]).
Definition nb := ([n0],[]).
Definition n2 := ([n1],[]).

Definition nd := (n_1::[n0],[]).
Definition ne := (n_1::[n1],[]).
Definition nf := (n0::[n1],[]).
Definition ng := (n_1::n0::[n1],[]).

Lemma is_num_abcdefg: 
is_number(na) /\ is_number(nb) /\ is_number(n2) /\ is_number(nd) /\
is_number(ne) /\ is_number(nf) /\ is_number(ng).
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

Lemma nums_hijklmn:
is_number(nh) /\ is_number(ni) /\ is_number(nj) /\ is_number(nk) /\
is_number(nl) /\ is_number(nm) /\ is_number(nn).
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


Definition bad_number (X Y Z: symbol) := (leq X Y /\ leq Y Z /\ ~leq X Z).

Lemma bad_numbers:
 forall (X Y Z: symbol), bad_number X Y Z ->
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
    split. { apply leq_def. split; eauto. }
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

Definition Dx (l: set symbol) : nat := fold_right (D) 0 l.

Lemma D_eq: forall (X: symbol) (n :nat), D X n = (S( max n ( max (Dx (left X)) (Dx (right X))))).
Proof.
intros X n; induction X as (l,l0); induction l; induction l0; induction n; unfold left; unfold right; simpl; tauto.
Qed.

Lemma D_ineq: forall (X: symbol) (n :nat), D X n >= D X 0.
Proof.
intros; induction n; repeat rewrite D_eq; lia.
Qed.

Lemma left_g: forall (X x: symbol), In x (left X) -> D X 0 > D x 0.
Proof.
intros; induction X as (l,l0); induction l; elim H; intros.
rewrite H0; rewrite D_eq; simpl; elim D_ineq; intros; lia.
apply IHl in H0; rewrite D_eq; simpl; rewrite D_eq; rewrite D_eq in H0; simpl in H0; lia.
Qed.

Lemma right_g: forall (X x: symbol), In x (right X) -> D X 0 > D x 0.
Proof.
intros; induction X as (l,l0); induction l0; elim H; intros.
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
intros; rewrite <- leq_def in H; apply not_and_or in H;
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
intro n; induction n.
intros; lia.
intros X H; pose proof (number X).
rewrite <- leq_def; split;
[rewrite forall_ngeq_l | rewrite forall_ngeq_r];
intros x H1; rewrite leq_n; intros H2;
cut (D x 0 < n); [ |apply left_g in H1; lia | |apply right_g in H1; lia ];
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
2:{induction (left X); elim H0; rewrite forall_ngeq_l in H; eauto.
  }
1:{
 elim (classic ( ngeq (left xl) [X])); eauto; intros; cut (False); tauto || auto;
 rewrite forall_ngeq_l in H1; apply not_all_ex_not in H1; destruct H1 as [xll];
 destruct H1; intros; rewrite leq_n; intros;
 cut (xll _<=_ xl).
 2:{ apply IHn; [apply left_g in H0; lia| auto].
    }
 1:{ intros; 
     cut (X _<=_ xl). 2:{ apply (T1 X xll xl); auto. }
     pose proof (number xl).
     intros; rewrite <- leq_def in H5; destruct H5; rewrite forall_ngeq_l in H5;
     apply (H5 xl) in H0; rewrite leq_n in H0; apply H0; apply (T3 xl); auto.
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
induction (right X); [elim H0| rewrite forall_ngeq_r in H; auto].

elim (classic ( ngeq [X] (right xr))); eauto; intros; cut (False); tauto || auto.
 rewrite forall_ngeq_r in H1; apply not_all_ex_not in H1; destruct H1 as [xrr].
 destruct H1; intros; rewrite leq_n; intros;
 cut (xr _<=_ xrr).
 2:{ apply IHn; [ apply right_g in H0; lia | auto].
    }
 1:{ intros; 
     cut (xr _<=_ X). 2:{ apply (T1 xr xrr X); auto. }
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
destruct (bad_numbers_leq_dec X Y); eauto.
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

Lemma ngeq_const_l: forall (X Y: set symbol) (x: symbol), ngeq X Y /\ ngeq [x] Y <-> ngeq (x:: X) Y.
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

Lemma ngeq_const_r: forall (X Y: set symbol) (y: symbol), ngeq X Y /\ ngeq X [y] <-> ngeq X (y::Y).
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



Lemma ngeq_concat_l: forall (X1 X2 Z: set symbol), ngeq X1 Z /\ ngeq X2 Z <-> ngeq (X1 ++ X2) Z.
Proof.
split.
induction X1;intros;repeat destruct H;auto.
rewrite <- ngeq_const_l in H; repeat destruct H; simpl; rewrite <- ngeq_const_l; auto.

induction X1.
simpl; intros; rewrite forall_ngeq_l; simpl; tauto.
simpl; intros; rewrite <- ngeq_const_l in H; repeat destruct H; rewrite <- ngeq_const_l; tauto.
Qed.

Lemma ngeq_concat_r: forall (X1 X2 Z: set symbol), ngeq Z X1 /\ ngeq Z X2 <-> ngeq Z (X1 ++ X2).
Proof.
split.
induction X1; intros; repeat destruct H; auto.

rewrite <- ngeq_const_r in H; repeat destruct H; simpl; rewrite <- ngeq_const_r; auto.

induction X1.
simpl; intros; rewrite forall_ngeq_r; simpl; tauto.
simpl; intros; rewrite <- ngeq_const_r in H; repeat destruct H; rewrite <- ngeq_const_r; tauto.
Qed.


Definition eqq (X Y: symbol) : Prop := leq X Y /\ leq Y X .

Lemma eqq_trans: 
forall (X Y Z: symbol), eqq X Y -> eqq Y Z -> eqq X Z.
Proof.
intros.
destruct H, H0.
split.
apply (T1 X Y Z); auto.
apply (T1 Z Y X); auto.
Qed.

Lemma eqq_sim: 
forall (X Y: symbol), eqq X Y <-> eqq Y X.
Proof.
split; intros; destruct H; split; auto.
Qed.


Lemma T7: 
forall (X:symbol) (Yl Yr: set symbol),  ngeq Yl [X] -> ngeq [X] Yr -> eqq X (pair ((left X) ++ Yl) ((right X) ++ Yr)).
Proof.
intros.
pose proof (T3 X) as P; apply leq_def in P; destruct P as [P1 P2].
pose proof (T3 (pair (left X ++ Yl) (right X ++ Yr))) as Q; apply leq_def in Q; destruct Q as [Q1 Q2]; simpl in Q1, Q2.
split; rewrite <- leq_def; simpl; split;
[ rewrite <- ngeq_concat_l in Q1 
| rewrite <- ngeq_concat_r 
| rewrite <- ngeq_concat_l 
| rewrite <- ngeq_concat_r in Q2
]; tauto.
Qed.

(** * Chapter 7: Discovery *)

(** * Chapter 8: Addition *)

Program Fixpoint plus (y:symbol) (x:symbol): symbol := 
match y with
| pair [] [] => x
| pair yl yr => let fix plusx (s:symbol): symbol:= 
                match s with
                | pair [] [] => y
                | pair xl xr => let fix plus_set (S: set symbol) (s:symbol): set symbol:= 
                                match S with
                                | [] => []
                                | h :: t => add (plus h s) (plus_set t s) 
                                end in
                                pair (union (plus_set yl x) (plus_set xl y)) (union (plus_set yr x) (plus_set xr y))
                end in
                plusx y
end.

Print plus.
Lemma Zero: plus n0 n0 = n0.
Proof.
auto.
Qed.

Lemma OnePlusOne: plus n1 n1 = pair [n1] [].
Proof.
auto.
Qed.

Lemma OnePlusOne2: (plus n1 n1)  = n2.
Proof.
auto.
Qed.

Program Fixpoint minus (x:symbol) : symbol := 
match x with
| pair [] [] => x
| pair l r => pair (map (minus) r) (map (minus) l)
end.

Definition subtract (y:symbol) (x:symbol) := plus y (minus x).

(** * Chapter 9: The Answer *)

(*
Lemma aux: forall (x1 x2 x3:symbol), [x1] _<_ [x2] -> [x2] _<_ [x3] -> eqq x2 ([x1], [x3]).
Proof.
intros.
pose proof (T7 x2 [x1] [x3] H H0) as T7_1.
pose proof (T7 ([x1], [x3]) (left x2) (right x2) ) as T7_2.
simpl in T7_2.
apply (eqq_trans x2 ((left x2 ++ [x1], right x2 ++ [x3])) ([x1],[x3])).
auto.
split.
apply eqq_sim.
*)


Lemma swap_s_ll: forall (x y w: list symbol) (z: symbol), (x++y, w) _<=_ z <-> (y++x, w) _<=_ z.
Proof.
cut (forall (x y w: list symbol) (z: symbol), (x++y, w) _<=_ z -> (y++x, w) _<=_ z).
split; auto.
cut (forall (n: nat) (x y w: list symbol) (z: symbol), D z 0 < n -> (x++y, w) _<=_ z -> (y++x, w) _<=_ z).
intros; apply (H (S(D z 0))); auto.
intro n; induction n.
lia.
intros x y w z P1 H; rewrite <- leq_def; rewrite <- leq_def in H; destruct H; split.
simpl; simpl in H; rewrite app_l_swap; auto.
clear H; rewrite forall_ngeq_r; rewrite forall_ngeq_r in H0; intros; assert (Ha := H); 
apply (H0 y0) in H; clear H0; apply leq_n; rewrite leq_n in H; 
rewrite <- leq_def; intros; destruct H0; elim H; clear H; rewrite <- leq_def; split.
clear H1; rewrite forall_ngeq_l; rewrite forall_ngeq_l in H0; intros; assert (Hb := H); 
apply (H0 x0) in H; clear H0; apply leq_n; rewrite leq_n in H; 
intros; elim H; clear H; 
apply (IHn x y w x0); pose proof (right_g z y0 Ha); pose proof (left_g y0 x0 Hb).
lia.
auto.
auto.
Qed.

Lemma swap_s_rl: forall (x y w: list symbol) (z: symbol), (x, y ++ w) _<=_ z <-> (x,w ++ y) _<=_ z.
Proof.
cut (forall (x y w: list symbol) (z: symbol), (x, y ++ w) _<=_ z -> (x, w ++ y) _<=_ z).
split; auto.
cut (forall (n: nat) (x y w: list symbol) (z: symbol), D z 0 < n -> (x, y ++ w) _<=_ z -> (x, w ++ y) _<=_ z).
intros; apply (H (S(D z 0))); auto.
intro n; induction n.
lia.
intros x y w z P1 H; rewrite <- leq_def; rewrite <- leq_def in H; destruct H; split;
auto.
clear H; rewrite forall_ngeq_r; rewrite forall_ngeq_r in H0; intros; assert (Ha := H).
apply (H0 y0) in H; clear H0; apply leq_n; rewrite leq_n in H; 
rewrite <- leq_def; intros; destruct H0; elim H; clear H; rewrite <- leq_def; split.
clear H1; rewrite forall_ngeq_l; rewrite forall_ngeq_l in H0; intros; assert (Hb := H); 
apply (H0 x0) in H; clear H0; apply leq_n; rewrite leq_n in H; 
intros; elim H; clear H; 
apply (IHn x y w x0); pose proof (right_g z y0 Ha); pose proof (left_g y0 x0 Hb).
lia.
auto.
simpl; simpl in H0; rewrite app_r_swap; auto.
Qed.

Lemma swap_s_lr: forall (x: symbol) (y w z: list symbol) ,  x _<=_ (y++w, z) <-> x _<=_ (w++y, z).
Proof.
cut (forall (x: symbol) (y w z: list symbol) ,  x _<=_ (y++w, z) -> x _<=_ (w++y, z)).
split; auto.
cut (forall (n: nat) (x: symbol) (y w z: list symbol), D x 0 < n -> x _<=_ (y++w, z) -> x _<=_ (w++y, z)).
intros; apply (H (S(D x 0))); auto.
intro n; induction n.
lia.
intros x y w z P1 H; rewrite <- leq_def; rewrite <- leq_def in H; destruct H; split.
2:{ simpl. simpl in H0. tauto. }
clear H0.

rewrite forall_ngeq_l. rewrite forall_ngeq_l in H. intros. assert (Ha := H0). 
apply (H x0) in H0. clear H; apply leq_n; rewrite leq_n in H0.
rewrite swap_s_ll.
auto. 
Qed.

Lemma swap_s_rr: forall (x: symbol) (y w z: list symbol) ,  x _<=_ (y, w++z) <-> x _<=_ (y, z++w).
Proof.
cut (forall (x: symbol) (y w z: list symbol) ,  x _<=_ (y, w++z) -> x _<=_ (y, z++w)).
split; auto.
cut (forall (n: nat) (x: symbol) (y w z: list symbol), D x 0 < n -> x _<=_ (y, w++z) -> x _<=_ (y, z++w)).
intros; apply (H (S(D x 0))); auto.
intro n; induction n.
lia.
intros x y w z P1 H; rewrite <- leq_def; rewrite <- leq_def in H; destruct H; split.
2:{ simpl. simpl in H0. rewrite app_r_swap. tauto. }
clear H0.
rewrite forall_ngeq_l. rewrite forall_ngeq_l in H. intros. assert (Ha := H0). 
apply (H x0) in H0. clear H; apply leq_n; rewrite leq_n in H0.
rewrite swap_s_rl.
auto. 
Qed.

Lemma T8: forall (y:symbol) (x:symbol), 
left y _<_ [x] -> 
[x] _<_ right y -> 
(forall (x0:symbol), left y _<_ [x0] ->  [x0] _<_ right y -> D x0 0 >= D x 0) ->
eqq x y.
Proof.
intros y x H H0 P.
cut (left x _<_ [y]).
cut ([y] _<_ right x).
pose proof (T7 x (left y) (right y) H H0) as T7a.
intros J0 J.
pose proof (T7 y (left x) (right x) J J0) as T7b.
apply (eqq_trans x (left x ++ left y, right x ++ right y) y).
auto.
clear T7a.
unfold eqq.
unfold eqq in T7b.
destruct T7b.
split.
rewrite swap_s_rl; rewrite swap_s_ll; auto.
rewrite swap_s_rr; rewrite swap_s_lr; auto.
1: {
rewrite forall_ngeq_r.
intro x0.
intros.
assert (Ha := H1).
apply right_g in H1.
rewrite -> leq_n.
rewrite <- leq_def.
intros.
destruct H2.
destruct (P x0).
apply T2_r in Ha.
clear H0 P H1 H2 H3.
rewrite forall_ngeq_l.
rewrite forall_ngeq_l in H.
intro y0.
intros.
apply (H y0) in H0.
apply (T5 y0 x x0);auto.
auto.
lia.
lia.
}

rewrite forall_ngeq_l.
intros.
assert (Ha := H1).
apply left_g in H1.
rewrite -> leq_n.
rewrite <- leq_def.
intros.
destruct H2.
destruct (P x0 H2).
apply T2_l in Ha.
clear H P H1 H2 H3.
rewrite forall_ngeq_r.
rewrite forall_ngeq_r in H0.
intros.
apply (H0 y0) in H.
apply (T6 x0 x y0);auto.
lia.
lia.
Qed.

