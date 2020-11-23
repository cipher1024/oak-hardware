

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
