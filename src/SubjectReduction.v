Require Import Program.Equality.
Require Vectors.Vector.
Import Vector.VectorNotations.
From Equations Require Import Equations.

Require Import Forall.
Require Import Types.
Require Import Processes.
Require Import Linearity.

Ltac lin_IH :=
  match goal with
  | [ H : Message bool TMT C[_] -> Message bool TMT C[_] ->
          Message bool TMT C[_] -> Message bool TMT C[_] ->
          _ |- _ ] =>
    destruct
      (H o o o o),
      (H x o o o),
      (H o x o o),
      (H o o x o),
      (H o o o x)
  | [ H : Message bool TMT C[_] -> Message bool TMT C[_] -> _ |- _ ] =>
    destruct
      (H o o),
      (H x o),
      (H o x)
  | [ H : Message bool TMT B[_] -> Message bool TMT C[_] -> _ |- _ ] =>
    destruct (H (V tt) o), (H (V tt) x)
  | [ H : Message bool TMT C[_] -> _ |- _ ] =>
    destruct (H o), (H x)
  end
.

Lemma congruence_linear {P Q} : Congruence _ _ P Q ->
  (single_x P -> single_x Q) /\ (lin P -> lin Q).
Proof.
  intros PcQ.
  induction PcQ; simp lin; try lin_IH; try tauto.
  - dependent destruction c; destruct b; destruct m; simp lin.
    + tauto.
    + destruct b; simp lin; tauto.
    + tauto.
    + destruct b; simp lin; tauto.
  - dependent destruction c; destruct b; destruct mt; lin_IH; simp lin; tauto.
Qed.
Hint Resolve congruence_linear.

Lemma branches_linear {n} (i : Fin.t n) {xs : Vector.t SType n}
      {Ps : Forall (fun s => Message _ _ C[s] -> Process _ _) xs} :
  (single_x (PBranch Ps (C false)) -> single_x (nthForall Ps i (C false))) /\
  (lin (PBranch Ps (C false)) -> single_x (nthForall Ps i (C true))) /\
  (lin (PBranch Ps (C false)) -> lin (nthForall Ps i (C false))).
Proof.
  induction i; dependent induction Ps; repeat split; intro H; destruct H.
  - auto.
  - destruct H0; auto.
  - auto.
  - decompose [and] (IHi v Ps); auto.
  - destruct H0; decompose [and] (IHi v Ps); auto.
  - destruct H0; decompose [and] (IHi v Ps); auto.
Qed.
Hint Resolve branches_linear.

Lemma reduction_linear {P Q} : Reduction _ _ P Q ->
  (single_x P -> single_x Q) /\ (lin P -> lin Q).
Proof.
  intro PrQ.
  induction PrQ; simp lin.
  - split; intro A; decompose [and or] A; (destruct m;
      [ destruct t; simp lin in *; tauto
      | destruct b; simp lin in *; tauto ]).
  - destruct (@branches_linear _ i rs Qs); split; intro A; decompose [and or] A; tauto.
  - lin_IH; tauto.
  - tauto.
  - destruct (congruence_linear H).
    tauto.
Qed.
Hint Resolve reduction_linear.

Theorem subject_reduction P Q : P ⇒ Q -> Linear P -> Linear Q.
Proof.
  intros PrQ lP.
  refine (
      (match (P bool TMT fMT) as P'
             return lin P' -> Reduction _ _ P' (Q bool TMT fMT) -> lin (Q bool TMT fMT)
       with
       | _ => _
       end) lP (PrQ bool TMT fMT)).
  intros slP sPrQ.
  destruct (reduction_linear sPrQ) as [_ lPlQ].
  exact (lPlQ lP).
Qed.
Hint Resolve subject_reduction.

Theorem big_step_subject_reduction P Q : P ⇒* Q -> Linear P -> Linear Q.
Proof.
  intros PrQ lP.
  refine (
      (match (P bool TMT fMT) as P'
             return lin P' -> RTReduction _ _ P' (Q bool TMT fMT) -> lin (Q bool TMT fMT)
       with
       | _ => _
       end) lP (PrQ bool TMT fMT)).
  intros slP sPrQ.
  induction sPrQ.
  auto.
  destruct (reduction_linear H); auto.
Qed.
Hint Resolve big_step_subject_reduction.
