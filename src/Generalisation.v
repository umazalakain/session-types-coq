Require Import Types.
Require Import Processes.
Require Import Linearity.

(******************************)
(*  PARAMETRIC GENERALISATION *)
(******************************)

Definition PProcess :=
  forall ST MT (mf : forall (S: Type), S -> Message ST MT B[S]),
    Process ST MT.
Notation "[ f ]> P" := (fun _ _ f => P)(at level 80).

Notation "P ≡ Q" := (forall ST MT mf, Congruence _ _ (P ST MT mf) (Q ST MT mf))(at level 80).
Notation "P ⇒ Q" := (forall ST MT mf, Reduction _ _ (P ST MT mf) (Q ST MT mf))(at level 80).
Notation "P ⇒* Q" := (forall ST MT mf, RTReduction _ _ (P ST MT mf) (Q ST MT mf))(at level 80).
Definition Linear (p : PProcess) : Prop := linear (p bool TMT fMT).
