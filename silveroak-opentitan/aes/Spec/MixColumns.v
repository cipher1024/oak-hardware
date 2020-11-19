
(****************************************************************************)
(* Copyright 2020 The Project Oak Authors                                   *)
(*                                                                          *)
(* Licensed under the Apache License, Version 2.0 (the "License")           *)
(* you may not use this file except in compliance with the License.         *)
(* You may obtain a copy of the License at                                  *)
(*                                                                          *)
(*     http://www.apache.org/licenses/LICENSE-2.0                           *)
(*                                                                          *)
(* Unless required by applicable law or agreed to in writing, software      *)
(* distributed under the License is distributed on an "AS IS" BASIS,        *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and      *)
(* limitations under the License.                                           *)
(****************************************************************************)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Cava.ListUtils.
Require Import Cava.VectorUtils.
Require Import Cava.Tactics.
Require Import Coq.Vectors.Fin.
Require Import Coq.Setoids.Setoid.
Import Vector.
Import VectorNotations.
Require Import Lia.
Require Import Psatz.
Require Import Coq.Program.Equality.
Require Import Coq.Program.Wf.

Set Implicit Arguments.

Module Matrix.
  Section MatrixDefs.

  Definition t A (n m : nat) := Vector.t (Vector.t A n) m.

  Context {A : Type} {m n k l : nat}.

  Definition mk {m n} (f : Fin.t m -> Fin.t n -> A) : t A m n :=
    vec_mk
      _ (fun i => vec_mk _ (fun j => f j i)).

  Fixpoint transpose {n} (x : t A m n) : t A n m :=
    match x with
    | nil _ => const (nil _) _
    | cons _ x n' xs => map2 (fun a => cons _ a n')  x (transpose xs)
    end.

  Definition nth {m n} (x : t A m n) i j := Vector.nth (Vector.nth x j) i.

  Definition row {m n} (x : t A m n) (i : Fin.t m) : Vector.t A n :=
    Vector.map (fun v => Vector.nth v i)  x.

  Definition col {m n} (x : t A m n) (i : Fin.t n) : Vector.t A m :=
    Vector.nth x i.

  Context (times plus : A -> A -> A) (zero : A).

  Definition sum {n} (v : Vector.t A n) : A :=
    Vector.fold_right plus v zero.

  Definition sprod {n} (v : Vector.t A n) (v' : Vector.t A n) : A :=
    sum (Vector.map2 times v v').

  Definition mul {m n k} (x : t A m n) (y : t A n k) : t A m k :=
    mk (fun i j => sprod (row x i) (col y j)).


  Lemma nth_mk (i : Fin.t m) (j : Fin.t n) (f : Fin.t m -> Fin.t n -> A) :
    nth (mk f) i j = f i j.
  Proof.
    unfold nth, mk. rewrite nth_vec_mk, nth_vec_mk. auto.
  Qed.

  (* Check nth. *)

  Hint Unfold nth.

  (* Check @nth_map. *)
  (* Check @nth_map2. *)

  Hint Rewrite @nth_map using solve [eauto] : vector.
  Hint Rewrite @nth_map2 using solve [eauto] : vector.
  Hint Rewrite @nth_mk : matrix.
  Hint Rewrite @nth_vec_mk : matrix.

  Lemma nth_transpose i j (x : t A m n) :
    nth (transpose x) i j = nth x j i.
  Proof.
    unfold nth. revert i j.
    induction x; intros i j.
    - inversion i.
    - simpl.
      erewrite nth_map2 by reflexivity.
      dependent destruction i;
       simpl; auto.
  Qed.

  Lemma nth_mul {m' n' k'}
        (x : t A m' n') (y : t A n' k') (i : Fin.t m') (j : Fin.t k') :
    nth (mul x y) i j =
    sprod (row x i) (col y j).
  Proof.
    unfold nth, mul, mk.
    rewrite nth_vec_mk, nth_vec_mk.
    auto.
  Qed.

  Lemma col_mul {m' n' k'}
        (x : t A m' n') (y : t A n' k') (j : Fin.t k') :
    col (mul x y) j = vec_mk _ (fun i => sprod (row x i) (col y j)).
    Admitted.

  Lemma row_mul {m' n' k'}
        (x : t A m' n') (y : t A n' k') (i : Fin.t m') :
    row (mul x y) i = vec_mk _ (fun j => sprod (row x i) (col y j)).
    Admitted.

  Print Fin.t.

  Lemma vext {A' n'} (x y : Vector.t A' n') (H : forall i, Vector.nth x i = Vector.nth y i) : x = y.
  Proof.
    induction n';
      dependent destruction x;
      dependent destruction y.
    - auto.
    - assert (H' := H (Fin.F1)).
      f_equal.
      + auto.
      + apply IHn'.
        intro i. apply (H (Fin.FS i)).
  Qed.

  Lemma ext {m' n'} (x y : t A m' n') (H : forall i j, nth x i j = nth y i j) : x = y.
  Proof.
    apply vext. intro i.
    apply vext. intro j.
    apply H.
  Qed.

  (* Fixpoint map_index {A B n} (f : Fin.t n -> A -> B) (v : Vector.t A n) : *)
  (*   Vector.t B n := *)
  (*   match v in Vector.t _ n' return (Fin.t n' -> A -> B) ->  Vector.t _ n' with *)
  (*   | nil _ => fun _ => nil _ *)
  (*   | cons _ x n' xs => *)
  (*     fun f' => cons _ (f' Fin.F1 x) n' *)
  (*                 (map_index (fun i => f' (Fin.FS i)) xs) *)
  (*   end f. *)

  Lemma map2_mk {B C} {n'} (v : Vector.t A n') (v' : Vector.t B n')
        (* (f : Fin.t n' -> B) :  *)
        (g : A -> B -> C) :
    map2 g v v' = vec_mk _ (fun i => g (v[@i]) (v'[@i])).
    Admitted.

  (* Lemma map2_mk' {B C} {n'} (v : Vector.t B n') *)
  (*       (f : Fin.t n' -> A) (g : A -> B -> C) : *)
  (*   map2 g (vec_mk _ f) v = map_index (fun i x => g (f i) x) v. *)
  (*   Admitted. *)

  Hint Rewrite @nth_mul : matrix.

  Hint Rewrite @col_mul : matrix.

  Hint Rewrite @row_mul : matrix.

  Hint Rewrite @map2_mk : matrix.

  (* Hint Rewrite @map2_mk' : matrix. *)

  Require Import Coq.Logic.FunctionalExtensionality.

  (* Check functional_extensionality. *)

  Check @vec_mk.
  (* @vec_mk *)
  (*      : forall (A : Type) (n : nat), (Fin.t n -> A) -> Vector.t A n *)

  Open Scope signature_scope.

  Require Import Coq.Classes.Morphisms.

  Print Proper.

  Section eqv.

  Context (eqA : A -> A -> Prop).

  Inductive vec_equiv : forall n, Vector.t A n -> Vector.t A n -> Prop :=
  | nil : vec_equiv (nil _) (nil _)
  | cons n x y xs ys : eqA x y -> vec_equiv xs ys -> vec_equiv (cons _ x n xs) (cons _ y n ys).


  Instance bar `{Reflexive A eqA} : Reflexive (vec_equiv (n := n)).
  Proof.
    intro x. induction x; constructor; auto.
  Qed.

  Instance bar0 `{Symmetric A eqA} : Symmetric (vec_equiv (n := n)).
  Proof.
    intros x y Hxy.
    induction Hxy; constructor; auto.
  Qed.

  Instance bar1 `{Transitive A eqA} : Transitive (vec_equiv (n := n)).
  Proof.
    intros x y z Hxy Hyz.
    induction Hxy.
    + destruct Hyz; constructor; auto.
    + dependent destruction Hyz. constructor; eauto.
  Qed.

  Instance vec_equiv_is_equiv `{Equivalence A eqA}  : Equivalence (vec_equiv (n := n)).
  Proof.
    destruct H.
    constructor.
    - intro x. induction x; constructor; auto.
    - intros x y Hxy.
      induction Hxy; constructor; auto.
    - intros x y z Hxy Hyz.
      induction Hxy.
      + destruct Hyz; constructor; auto.
      + dependent destruction Hyz. constructor.
        * eauto.
        * auto.
  Qed.

  Instance foo `{Equivalence A eqA} : Proper (pointwise_relation _ eqA ==> (vec_equiv (n := n))) (@vec_mk A n).
  Proof.
    intros f g H'.
    induction n; simpl; constructor.
    - auto.
    - apply IHn0. intro i.
      auto.
  Qed.

  Add Parametric Relation `{Equivalence A eqA} : (Vector.t A n) (@vec_equiv n)
      reflexivity proved by (bar )
      symmetry proved by bar0
      transitivity proved by bar1
        as vec_eqv_rel
  .

  Add Parametric Morphism `{Equivalence A eqA} : (@vec_mk A n)
      with signature (@pointwise_relation (Fin.t n) A eqA ==> vec_equiv (n := n)) as
          foo3.
  Proof.
    apply foo.
  Qed.

  Context (Hplus_congr : forall x x' y y' : A, eqA x y -> eqA x' y' -> eqA (plus x x') (plus y y')).

  Add Parametric Morphism `{Equivalence A eqA} : (@sum n)
      with signature (vec_equiv (n := n) ==> eqA) as
          foo5.
  Proof.
    intros x y Hxy.
    induction Hxy. reflexivity.
    - unfold sum. simpl.
      auto using Hplus_congr.

  Qed.

  Lemma mul_assoc {x : t A m n} {y : t A n k} {z : t A k l} :
    mul x (mul y z) = mul (mul x y) z.
  Proof.
    apply ext. intros i j.
    autorewrite with matrix.
    unfold sprod.

    autorewrite with matrix.
    (* setoid_rewrite nth_vec_mk. *)
  Abort.

End eqv.
  End MatrixDefs.
End Matrix.

Section Spec.
  Context {byte : Type}
          (zero one : byte)
          (add smul sub div : byte -> byte -> byte)
          (opp inv : byte -> byte)
          (* (mul : nat -> byte -> byte) *)
          (lift : nat -> byte).

  Require Import Coq.Bool.Bool.

  Search( _ =? _).
  Check reflect.

  Program Fixpoint xor (x y : nat) {measure x} : nat :=
    match Nat.eqb_spec x 0 with
    | ReflectT _ H => y
    | ReflectF _ H =>
      ((x + y) mod 2) + 2*(xor (x / 2) (y / 2))
    end .
  Next Obligation.
    assert (H' := Nat.divmod_spec x 1 0 1 ltac:(reflexivity)).
    destruct (Nat.divmod x 1 0 1) as [a b].
    destruct H' as [H0 H1].
    simpl in *. lia.
  Qed.

  Definition mul (i : nat) (b : byte) : byte :=
    smul (lift i) b.

  Open Scope vector_scope.

  Ltac nat_to_fin x :=
    match goal with
    | |- Fin.t ?k => apply (@Fin.of_nat_lt x k); lia
    end.

  Infix "⊕" := (add)(left associativity, at level 45).
  Infix "∙" := (mul)(at level 43, left associativity).
  (* Notation "\[[ x \]]" := (@Fin.of_nat_lt _ x ltac:(lia)). *)

  Notation "\[ x \]" := (ltac:(nat_to_fin x))(only parsing).
  Notation "\[ x \]" := (@Fin.of_nat_lt x _ _)(only printing).
  Definition col := (byte * byte * byte * byte)%type.
  (* Definition col := Vector.t byte 4. *)


  Check @Fin.of_nat_lt.

  Check ( \[ 3 \] : Fin.t 7).
  Check nth.

  Definition MixColumns (c : col) : col :=
    match c with
    | (c0,c1,c2,c3) =>
      (2 ∙ c0 ⊕ 3 ∙ c1 ⊕ 1 ∙ c2 ⊕ 1 ∙ c3,
       1 ∙ c0 ⊕ 2 ∙ c1 ⊕ 3 ∙ c2 ⊕ 1 ∙ c3,
       1 ∙ c0 ⊕ 1 ∙ c1 ⊕ 2 ∙ c2 ⊕ 3 ∙ c3,
       3 ∙ c0 ⊕ 1 ∙ c1 ⊕ 1 ∙ c2 ⊕ 2 ∙ c3)
    end.


  Definition InvMixColumns (c : col) : col :=
    match c with
    | (c0,c1,c2,c3) =>
      (14 ∙ c0 ⊕ 11 ∙ c1 ⊕ 13 ∙ c2 ⊕  9 ∙ c3,
        9 ∙ c0 ⊕ 14 ∙ c1 ⊕ 11 ∙ c2 ⊕ 13 ∙ c3,
       13 ∙ c0 ⊕  9 ∙ c1 ⊕ 14 ∙ c2 ⊕ 11 ∙ c3,
       11 ∙ c0 ⊕ 13 ∙ c1 ⊕  9 ∙ c2 ⊕ 14 ∙ c3)
    end.

  Context (Hdistrib : forall x y z, x ∙ (y ⊕ z) = x ∙ y ⊕ x ∙ z).
  Context (Hfoo : forall x y z, x ∙ (y ∙ z) = (x * y) ∙ z).
  Context (Hassoc : forall x y z, x ⊕ (y ⊕ z) = (x ⊕ y) ⊕ z).

  Lemma Hdistrib' : forall x y z, (xor y z) ∙ x = y ∙ x ⊕ z ∙ x.
    Admitted.

  Lemma Hdistrib'' : forall x y z k, k ⊕ (xor y z) ∙ x = k ⊕ y ∙ x ⊕ z ∙ x.
    Admitted.

  Import ListNotations.
  Local Open Scope list_scope.

  Fixpoint poly (xs : list (nat * byte)%type) : byte :=
    match xs with
    | ([])%list => zero
    | ((x, k):: xs) => x ∙ k ⊕ poly xs
    end.

  Lemma poly_mk x y :
    x ∙ y = poly [(x, y)].
  Admitted.

  Lemma poly_app xs ys :
    poly xs ⊕ poly ys = poly (xs ++ ys).
  Admitted.

  Variables
    Hlift : forall x y, mul x y = smul (lift x) y.

  Hint Rewrite @Hdistrib : foo.
  Hint Rewrite @Hfoo : foo.
  Hint Rewrite @Hassoc : foo.
  (* Hint Rewrite @poly_mk : bar. *)
  (* Hint Rewrite @poly_app : bar. *)
  (* Hint Rewrite @Hlift : foo_bar. *)

  (* Ltac  *)

  Ltac poly_swap x y :=
    match goal with
    | |- context [ poly ?a ] =>
      match a with
      | ((?a, x) :: (?b, y) :: ?xs)%list =>
        assert (H : poly ((x :: y :: xs)) = poly ((y :: x :: xs)) )
      | _ => fail "bar"
      end
    end.

  Require Import Ring Field.

  Check ring_theory zero one add smul sub opp eq.

  Variables foo : field_theory zero one add smul sub opp div inv eq.
  (* Variables foo : ring_theory zero one add smul sub opp eq. *)

  Context (Hcomm : forall x y, x ⊕ y = y ⊕ x).

  Add Field byte : foo.

  Lemma Hcomm' x y k : k ⊕ x ⊕ y = k ⊕ y ⊕ x.
    Admitted.

  Ltac foo c :=
    match goal with
    | |- context f [ ?a ∙ c ⊕ ?b ∙ c ] => rewrite <- (Hdistrib' c a b)
    | |- context f [ ?k ⊕ ?a ∙ c ⊕ ?b ∙ c ] => rewrite <- (Hdistrib'' c a b k)
    | |- context f [ ?a ∙ ?x ⊕ ?b ∙ c ] => rewrite (Hcomm (a ∙ x) (b ∙ c))
    | |- context f [ ?k ⊕ ?a ∙ ?x ⊕ ?b ∙ c ] => rewrite (Hcomm' (a ∙ x) (b ∙ c) k)
    end.

  Search xor.


  Lemma InvMixColumns_MixColumns (c : col) :
    InvMixColumns (MixColumns c) = c.
  Proof.
    destruct c as [ [[c0 c1] c2] c3 ].
    simpl. repeat f_equal.
    all: autorewrite with foo.

    all: repeat foo c0.
    all: repeat foo c1.
    all: repeat foo c2.
    all: repeat foo c3.
      simpl.
    compute.

    Eval compute in 2^8 + 2^4 + 2^3 + 1.

Qed.

    foo c1.
    foo c1.
    foo c1.
    foo c1.
    foo c1.

    all: autorewrite with foo_bar.
    (* all: unfold app. *)

    (* poly_swap c0 c1. *)

    all: simpl.
    ring_simplify c0.
    field. ring.

    ring_simplify.
