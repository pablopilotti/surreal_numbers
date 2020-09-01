Require Import List.
Import ListNotations.
Require Import Classical.
Require Import Classical_Prop.
Require Import Init.Logic.


(* Definion de Simbolos *)
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

(* Ejemplo de Simbolos *)
Definition n0 := ([],[]).
Definition n_1 := ([],[n0]).
Definition n1 := ([n0],[]).

(* Definicion de: No es mayor o igual *)
Axiom ngeq: list symbol-> list symbol -> Prop.
Axiom forall_ngeq_r: forall (X Y: list symbol), ngeq X Y <-> forall (y: symbol), In y Y -> ngeq X [y].
Axiom forall_ngeq_l: forall (X Y: list symbol), ngeq X Y <-> forall (x: symbol), In x X -> ngeq [x] Y.

(* Definicion de: Es menor o igual *)
Axiom leq: symbol-> symbol -> Prop.
Axiom leq_def: forall (X: symbol), forall (Y: symbol), (ngeq (left X) [Y] /\ ngeq [X] (right Y)) <-> leq X Y.

(* TODO mejorar la notacion *)
Notation "x _<=_ y" := (leq x y)
                     (at level 60, right associativity).
Notation "~ ( x _>=_  y )" := (ngeq x y)
                     (at level 60, right associativity).

(* Definicion de: Es menor o igual *)
Axiom leq_n: forall (X: symbol), forall (Y: symbol), ngeq [Y] [X] <-> (leq X Y -> False).
Axiom ngeq_n: forall (X: symbol), forall (Y: symbol), leq X Y <-> (ngeq [Y] [X] -> False).

Check ngeq_n.

Definition is_number (x: symbol) := ngeq (left x) (right x).

(*Pruebas de que 0, 1 y -1 son numeros y 0 <= 0, *)
Lemma Zero_is_number: (is_number n0).
Proof.
  (* unfold is_number. unfold n0. unfold left.*)
  apply forall_ngeq_l. intros. tauto.
Qed.


Lemma One_is_number: (is_number n1).  Proof. (* unfold is_number. unfold n1. unfold n0. unfold right. *) apply forall_ngeq_r. intros. tauto. Qed.
Lemma minusOne_is_number: (is_number n_1). Proof. unfold is_number. unfold n_1. unfold n0. unfold left. apply forall_ngeq_l. intros. tauto. Qed.
Lemma leq_Zero_Zero: leq n0 n0. Proof. unfold n0. apply leq_def. split. unfold left. apply forall_ngeq_l. intros. tauto. unfold right. apply forall_ngeq_r. intros. tauto.  Qed.
Lemma leq_minusOne_Zero: leq n_1 n0. Proof. unfold n_1. unfold n0. apply leq_def. split. unfold left. apply forall_ngeq_l. intros. tauto. unfold right. apply forall_ngeq_r. intros. tauto.  Qed.
Lemma leq_Zero_minusOne: (leq n0 n1). Proof. unfold n1. unfold n0. apply leq_def. split. unfold left. apply forall_ngeq_l. intros. tauto. unfold right. apply forall_ngeq_r. intros. tauto.  Qed.
Lemma leq_minusOne_One: leq n_1 n1. Proof. unfold n_1. unfold n1. unfold n0. apply leq_def. split. unfold left. apply forall_ngeq_l. intros. tauto. unfold right. apply forall_ngeq_r. intros. tauto. Qed.
Lemma no_leq_Zero_minusOne: leq n0 n_1->False. Proof. intros. apply (leq_n n0 n0). apply leq_def in H. destruct H. eauto. apply leq_Zero_Zero. Qed.


Definition bad_number(X Y Z: symbol):= leq X Y /\ leq Y Z /\ ~leq X Z.


(* ----------------- Lemas auxiliares -----------------*)
Lemma not_leq_to_or: forall (X Y: symbol), (leq X Y -> False) -> ((ngeq (left X) [Y]-> False) \/ (ngeq [X] (right Y) ->False)).
Proof.
intros.
elim (classic ((ngeq (left X) [Y] /\ ngeq [X] (right Y)))) ; [ intros ; apply leq_def in H0 |] ; tauto.
Qed.

(* No encuentro este teorema en mi libreria *)
Theorem not_iff_compat : forall A B : Prop,
  (A <-> B) -> (~ A <-> ~B).
Proof.
tauto.
Qed.

Lemma not_forall_ngeq_l: forall (x Y: symbol),forall (X: list symbol), (~ ngeq X [Y]) <->  ((~ forall x : symbol, (In x X -> ngeq [x] [Y]))).
Proof.
intros.
apply not_iff_compat.
apply forall_ngeq_l.
Qed.


Lemma not_forall_exists_not_l: forall (x Y: symbol),forall (X: list symbol),
             ((~ forall x : symbol, In x X -> ngeq [x] [Y])) ->
             ((exists x : symbol, In x X -> (ngeq [x] [Y]->False))).
Proof.
intros.
apply not_all_ex_not in H.
unfold not in H.
elim H.
intros.
exists x0.
tauto.
Qed.

Lemma not_forall_ngeq_r: forall (y X: symbol),forall (Y: list symbol), (~ ngeq [X] Y) <->  ((~ forall y : symbol, (In y Y -> ngeq [X] [y]))).
Proof.
intros.
apply not_iff_compat.
apply forall_ngeq_r.
Qed.


Lemma not_forall_exists_not_r: forall (y X: symbol),forall (Y: list symbol),
             ((~ forall y : symbol, In y Y -> ngeq [X] [y])) ->
               ((exists y : symbol, In y Y -> (ngeq [X] [y]->False))).
Proof.
intros.
apply not_all_ex_not in H.
unfold not in H.
elim H.
intros.
exists x.
tauto.
Qed.
(* ----------------- Lemas auxiliares -----------------*)

Lemma bad_numbers: forall (X Y Z: symbol), bad_number X Y Z ->
               (exists x : symbol, In x (left X) -> bad_number Y Z x) \/
               (exists z : symbol, In z (right Z) ->bad_number z X Y).

Proof.
  unfold bad_number.
  intros.
  destruct H.
  destruct H0.
  apply not_leq_to_or in H1.
  destruct H1.
  {
    left.
    apply leq_def in H.
    apply leq_def in H0.
    destruct H.
    destruct H0.
    apply not_forall_ngeq_l in H1 ; last easy.
    apply not_forall_exists_not_l in H1 ; last easy.
    elim H1.
    {
      intros.
      exists x.
      intros.
      split.
      {
        apply leq_def.
        split;  eauto.
      }
      {
        split ; first  (apply ngeq_n ; eauto).
        unfold not.
        apply leq_n.
        rewrite (forall_ngeq_l (left X) [Y]) in H.
        eauto.
      }
    }
  }
  {
    right.
    apply leq_def in H.
    apply leq_def in H0.
    destruct H.
    destruct H0.
    apply not_forall_ngeq_r in H1 ; last easy.
    apply not_forall_exists_not_r in H1 ; last easy.
    elim H1.
    intros z.
    intros.
    exists z.
    intros.
    split ; first (apply ngeq_n ; eauto).
    split ; first (apply leq_def ; eauto).
    unfold not.
    apply leq_n.
    rewrite (forall_ngeq_r [Y] (right Z)) in H3.
    eauto.
  }
Qed.


(* dia de creacion *)
Fixpoint count_s (s:symbol) : nat :=
  let count_l := (fix count_l (l: list symbol) : nat :=
                  match l with
                    | []   => 0
                    | s::l => max (count_s s) (count_l l)
                  end) in
  match s with
  | pair x y  => 1 + max (count_l x) (count_l y)
  end.

Lemma p : count_s n1 = count_s n_1.
Proof.
unfold n_1, n1, n0. unfold count_s. eauto.
Qed.
