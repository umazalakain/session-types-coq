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
  | [ s : SType, r : SType , s' : SType, r' : SType |- _ ] =>
    match goal with
    | [ H : Message bool TMT C[s] -> Message bool TMT C[r] ->
            Message bool TMT C[s'] -> Message bool TMT C[r'] ->
            _ |- _ ] =>
      destruct (H o o o o);
      destruct (H x o o o);
      destruct (H o x o o);
      destruct (H o o x o);
      destruct (H o o o x)
    end
  | [ s : SType, r : SType |- _ ] =>
    match goal with
    | [ H : forall (a : Message bool TMT C[s]) (b : Message bool TMT C[r]), _ |- _ ] =>
      destruct (H o o);
      destruct (H o x);
      destruct (H x o)
    end
  | [ T : Type, s : SType |- _ ] =>
    match goal with
    | [ H : forall (a : Message bool TMT B[T]) (b : Message bool TMT C[s]), _ |- _ ] =>
      destruct (H (V tt) o);
      destruct (H (V tt) x)
    end
  | [ s : SType |- _ ] =>
    match goal with
    | [ H : forall (a : Message bool TMT C[s]), _ |- _ ] =>
      destruct (H o);
      destruct (H x)
    end
  end
.

Theorem congruence_linear {P Q} : Congruence _ _ P Q ->
  (single_x P -> single_x Q) /\ (lin P -> lin Q).
Proof.
  intros PcQ.
  induction PcQ; split; simp lin in *; try lin_IH; try tauto.
  - dependent destruction c; destruct b; destruct m; simp lin in *.
    + tauto.
    + destruct b; simp lin; tauto.
    + destruct b; simp lin; tauto.
  - dependent destruction c; destruct b; destruct m; simp lin in *.
    + tauto.
    + destruct b; simp lin; tauto.
  - dependent destruction c;
      destruct b;
      destruct mt;
      simp lin in *;
      lin_IH;
      tauto.
  - dependent destruction c;
      destruct b;
      destruct mt;
      simp lin in *;
      lin_IH;
      tauto.
Qed.
Hint Resolve congruence_linear.

Lemma branches_linear {n} (i : Fin.t n) {xs : Vector.t SType n}
      {Ps : Forall (fun s => Message _ _ C[s] -> Process _ _) xs} :
  (single_x (PBranch Ps (C false)) -> single_x (nthForall Ps i (C false))) /\
  (lin (PBranch Ps (C false)) -> single_x (nthForall Ps i (C true))) /\
  (lin (PBranch Ps (C false)) -> lin (nthForall Ps i (C false))).
Proof.
  induction i; dependent induction Ps; repeat split; intro H; simp lin in *.
  - destruct H.
    assumption.
  - destruct H.
    destruct H0.
    assumption.
  - destruct H.
    destruct H0.
    assumption.
  - destruct H.
    decompose [and] (IHi v Ps).
    auto.
  - destruct H.
    destruct H0.
    decompose [and] (IHi v Ps).
    auto.
  - destruct H.
    destruct H0.
    decompose [and] (IHi v Ps).
    auto.
Qed.
Hint Resolve branches_linear.

Theorem reduction_linear {P Q} : Reduction _ _ P Q ->
  (single_x P -> single_x Q) /\ (lin P -> lin Q).
Proof.
  intro PrQ.
  induction PrQ; split; simp lin in *.
  - intro A; destruct A; (destruct m;
      [ destruct t; simp lin in *; tauto
      | destruct b; simp lin in *; tauto ]).
  - intro A.
    decompose [and or] A; try contradiction.
    destruct m;
      [ destruct t; simp lin in *; tauto
      | destruct b; simp lin in *; tauto ].
  - destruct (@branches_linear _ i rs Qs).
    intro A.
    decompose [and or] A; tauto.
  - decompose [and] (@branches_linear _ i rs Qs).
    intro A.
    decompose [and or] A; tauto.
  - lin_IH; tauto.
  - lin_IH; tauto.
  - tauto.
  - tauto.
  - destruct (congruence_linear H).
    tauto.
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
