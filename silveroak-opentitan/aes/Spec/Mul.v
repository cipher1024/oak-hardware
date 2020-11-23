

From mathcomp Require Import algebra.poly.
From mathcomp Require Import field.galois.
From mathcomp Require Import field.finfield.
From mathcomp Require Import algebra.matrix.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype div tuple bigop prime finset fingroup.
From mathcomp Require Import ssralg poly polydiv morphism action finalg zmodp.
(* From mathcomp Require Import cyclic center pgroup abelian matrix mxpoly vector. *)
(* From mathcomp Require Import falgebra fieldext separable galois. *)
(* From mathcomp Require ssrnum ssrint algC cyclotomic. *)

Require Import Cava.ListUtils.


Import GroupScope GRing.Theory FinRing.Theory.
Local Open Scope ring_scope.
Set Implicit Arguments.
Unset Strict Implicit.

Variable F : finFieldType.
Variables p : Vector.t F 8.

Section Vec.

Import Vector.

Fixpoint eval {n} (p : Vector.t F n) (x : F) : F :=
  match p with
  | nil => 0
  | cons a n' bs => a * x^+n' + eval bs x
  end.

End Vec.

Open Scope list_scope.

Require Import Lists.List.
Import ListNotations.

Definition smul (x : F) (ys : list F) : list F :=
map (fun y => x * y) ys.

Fixpoint map2_left {A B} (f : A -> B -> A) (xs : list A) (ys : list B) : list A :=
  match xs, ys with
  | _, [] => xs
  | [], _ => []
  | (x :: xs), (y :: ys) => f x y :: map2_left f xs ys
  end.

Lemma map2_left_length {A B} (f : A -> B -> A) xs ys :
  length (map2_left f xs ys) = length xs.
Proof.
  revert ys.
  induction xs as [| x xs]; intro ys.
  - simpl. destruct ys; auto.
  - simpl. destruct ys.
    + auto.
    + simpl. rewrite IHxs. auto.
Qed.

Definition add_msb (xs ys : list F) : list F :=
  map2_left (fun x y : F => x + y) (0 :: xs) ys.

Fixpoint prod (xs ys : list F) : list F :=
  match xs with
  | [] => repeat 0 (length ys)
  | (x :: xs) => add_msb (prod xs ys) (smul x ys)
  end.

Fixpoint eval' (p : list F) (x : F) : F :=
  match p with
  | [] => 0
  | (a :: bs) => a * x^+length bs + eval' bs x
  end.

Module Import GRing.
(* Import Ring.Exports. *)

(* Import Field.Exports. *)

Check left_zero.

Hint Opaque map2_left.

Lemma prod_nil xs a : eval' (prod xs []) a = 0.
Proof.
  induction xs; simpl.
  - auto.
  - rewrite mul0r. rewrite IHxs. rewrite add0r => //.
Qed.

Require ssrsearch.
Require Import  Coq.Init.Nat.


Lemma length_prod xs ys : length (prod xs ys) = (length xs + length ys)%nat.
Proof.
  induction xs; simpl.
  - rewrite repeat_length. auto.
  - remember (smul a ys) as zs. destruct zs as [| z zs].
    + simpl.  rewrite IHxs. auto.
    + simpl. rewrite map2_left_length. rewrite IHxs. auto.
Qed.

(* Open Scope nat_scope. *)

Hint Rewrite @mul0r : ring.
Hint Rewrite @mulr0 : ring.

Hint Rewrite @mul1r : ring.
Hint Rewrite @mulr1 : ring.

Hint Rewrite @add0r : ring.
Hint Rewrite @addr0 : ring.

Hint Rewrite @expr0 : ring.
Hint Rewrite @expr1 : ring.
Hint Rewrite @exprS : ring.
Hint Rewrite @exp0n : ring.
Hint Rewrite @exp1n : ring.

(* Lemma eval_add_msg xs ys a *)
(*       (H : length ys <= length xs) : *)
(*   eval' (add_msb xs ys) a = eval' xs a + eval' ys a * a^+(length xs - length ys)%nat. *)
(* Proof. *)
(*   revert ys H. *)
(*   induction xs as [| x xs]; intros ys H. *)
(*   - simpl. destruct ys; simpl. *)
(*     + rewrite mul0r. auto. *)
(*     + destruct ys; simpl. autorewrite with ring. done. *)
(*     + simpl in H. inversion H. *)
(*   - simpl. destruct ys; simpl. *)
(*     + autorewrite with ring. done. *)
(*       destruct ys. simpl. autorewrite with ring. *)
(*       ring. *)
(*       rewrite expr0. rewrite mulr1. auto. *)

Goal forall (xs ys : list F) (a : F), eval' (prod xs ys) a = eval' xs a * eval' ys a.
Proof.
  intros. revert ys.
  induction xs as [| x xs]; intro ys.
  - simpl. rewrite mul0r. auto.
  - induction ys as [| y ys].
    + simpl. auto.
    + simpl. rewrite mul0r. rewrite IHys. rewrite add0r. auto.
    (* + simpl. remember (smul x ys) as zs. *)
      destruct ys as [| y ys ].
      * simpl. rewrite mul0r. rewrite prod_nil. rewrite mulr0. rewrite add0r => //.
      * simpl prod. simpl eval'.
      (*   unfold prod. simpl. rewrite map2_left_length. *)
      (* fold prod. *)
