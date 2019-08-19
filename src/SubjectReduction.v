Require Import Program.Equality.
Require Vectors.Vector.
Import Vector.VectorNotations.
From Equations Require Import Equations.

Require Import Forall.
Require Import Types.
Require Import Processes.
Require Import Linearity.
Require Import Generalisation.

Ltac linearity_hypotheses :=
  match goal with
  | [ s : SType, r : SType , s' : SType, r' : SType |- _ ] =>
    match goal with
    | [ H : Message bool TMT C[s] -> Message bool TMT C[r] ->
            Message bool TMT C[s'] -> Message bool TMT C[r'] ->
            _ |- _ ] =>
      destruct (H unmarked unmarked unmarked unmarked);
      destruct (H marked unmarked unmarked unmarked);
      destruct (H unmarked marked unmarked unmarked);
      destruct (H unmarked unmarked marked unmarked);
      destruct (H unmarked unmarked unmarked marked)
    end
  | [ s : SType, r : SType |- _ ] =>
    match goal with
    | [ H : forall (a : Message bool TMT C[s]) (b : Message bool TMT C[r]), _ |- _ ] =>
      destruct (H unmarked unmarked);
      destruct (H unmarked marked);
      destruct (H marked unmarked)
    end
  | [ T : Type, s : SType |- _ ] =>
    match goal with
    | [ H : forall (a : Message bool TMT B[T]) (b : Message bool TMT C[s]), _ |- _ ] =>
      destruct (H (V tt) unmarked);
      destruct (H (V tt) marked)
    end
  | [ s : SType |- _ ] =>
    match goal with
    | [ H : forall (a : Message bool TMT C[s]), _ |- _ ] =>
      destruct (H unmarked);
      destruct (H marked)
    end
  end
.

Theorem congruence_linear {P Q} : Congruence _ _ P Q ->
  (single_marked P -> single_marked Q) /\ (linear P -> linear Q).
Proof.
  intros PcQ.
  induction PcQ; split; simp linear in *; try linearity_hypotheses; try tauto.
  - dependent destruction c; destruct b; destruct m; simp linear in *.
    + tauto.
    + destruct b; simp linear; tauto.
    + destruct b; simp linear; tauto.
  - dependent destruction c; destruct b; destruct m; simp linear in *.
    + tauto.
    + destruct b; simp linear; tauto.
  - dependent destruction c;
      destruct b;
      destruct mt;
      simp linear in *;
      linearity_hypotheses;
      tauto.
  - dependent destruction c;
      destruct b;
      destruct mt;
      simp linear in *;
      linearity_hypotheses;
      tauto.
Qed.
Hint Resolve congruence_linear.

Lemma branches_linear {n} (i : Fin.t n) {xs : Vector.t SType n}
      {Ps : Forall (fun s => Message _ _ C[s] -> Process _ _) xs} :
  (single_marked (PBranch Ps (C false)) -> single_marked (nthForall Ps i (C false))) /\
  (linear (PBranch Ps (C false)) -> single_marked (nthForall Ps i (C true))) /\
  (linear (PBranch Ps (C false)) -> linear (nthForall Ps i (C false))).
Proof.
  induction i; dependent induction Ps; repeat split; intro H; simp linear in *.
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
  (single_marked P -> single_marked Q) /\ (linear P -> linear Q).
Proof.
  intro PrQ.
  induction PrQ; split; simp linear in *.
  - intro A; destruct A; (destruct m;
      [ destruct t; simp linear in *; tauto
      | destruct b; simp linear in *; tauto ]).
  - intro A.
    decompose [and or] A; try contradiction.
    destruct m;
      [ destruct t; simp linear in *; tauto
      | destruct b; simp linear in *; tauto ].
  - destruct (@branches_linear _ i rs Qs).
    intro A.
    decompose [and or] A; tauto.
  - decompose [and] (@branches_linear _ i rs Qs).
    intro A.
    decompose [and or] A; tauto.
  - linearity_hypotheses; tauto.
  - linearity_hypotheses; tauto.
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
             return linear P' -> Reduction _ _ P' (Q bool TMT fMT) -> linear (Q bool TMT fMT)
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
             return linear P' -> RTReduction _ _ P' (Q bool TMT fMT) -> linear (Q bool TMT fMT)
       with
       | _ => _
       end) lP (PrQ bool TMT fMT)).
  intros slP sPrQ.
  induction sPrQ.
  auto.
  destruct (reduction_linear H); auto.
Qed.
Hint Resolve big_step_subject_reduction.
