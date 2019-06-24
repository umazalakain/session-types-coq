Require Import Program.Equality.
Require Vectors.Vector.
Require Vectors.Fin.
Import Vector.VectorNotations.

Inductive Forall {A} (P: A -> Type): forall {n} (v: Vector.t A n), Type :=
 |Forall_nil: Forall P []
 |Forall_cons {n} x (v: Vector.t A n): P x -> Forall P v -> Forall P (x::v).
Hint Constructors Forall.

Inductive Forall2 {A B} (P:A->B->Type): forall {n}, Vector.t A n -> Vector.t B n -> Type :=
 |Forall2_nil: Forall2 P [] []
 |Forall2_cons {m} x1 x2 (v1:Vector.t A m) v2: P x1 x2 -> Forall2 P v1 v2 ->
    Forall2 P (x1::v1) (x2::v2).
Hint Constructors Forall2.

Definition nthForall : forall {A P n} {xs : Vector.t A n}
                         (ps : Forall P xs) (i : Fin.t n), P xs[@i].
Proof.
  intros A P n xs ps i.
  dependent induction ps; dependent induction i; eauto.
Qed.

Definition nthForall2 : forall {A B P n} {xs : Vector.t A n} {ys : Vector.t B n}
                          (ps : Forall2 P xs ys) (i : Fin.t n), P xs[@i] ys[@i].
Proof.
  intros A B P n xs ys ps i.
  dependent induction ps; dependent induction i; eauto.
Qed.
