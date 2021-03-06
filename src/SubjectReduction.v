Require Import Program.Equality.
Require Vectors.Vector.
Import Vector.VectorNotations.
From Equations Require Import Equations.

Require Import Forall.
Require Import Types.
Require Import Processes.
Require Import Linearity.

Lemma congruence_linear {P Q} : Congruence _ _ P Q ->
  (single_x P -> single_x Q) /\ (lin P -> lin Q).
Proof.
  intros PcQ; induction PcQ; simp lin; intuition.
Qed.
Hint Resolve congruence_linear.

Lemma rtcongruence_linear {P Q} : RTCongruence _ _ P Q ->
  (single_x P -> single_x Q) /\ (lin P -> lin Q).
Proof.
  intro PcQ; induction PcQ; intuition; destruct (congruence_linear H); auto.
Qed.
Hint Resolve rtcongruence_linear.

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
  - destruct (H0 o o), (H0 x o), (H0 o x); tauto.
  - tauto.
  - destruct (rtcongruence_linear H).
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
