Require Import Program.Equality.
From Equations Require Import Equations.

Require Import Types.
Require Import Processes.
Require Import Linearity.

Ltac constructors :=
  repeat (intros; compute; constructor)
.
Hint Extern 1 (Duality _ _) => constructors.
Hint Extern 1 (_ ≡ _) => constructors.
Hint Extern 1 (_ ≡* _) => intros; econstructor.
Hint Extern 1 (RTCongruence _ _ _ _) => econstructor.
Hint Extern 1 (Congruence _ _ _ _) => constructors.
Hint Constructors Congruence.
Hint Constructors RTCongruence.

Ltac not_duality :=
  intro;
  match goal with
  | [ H : Duality _ _ |- False ] => repeat (dependent induction H)
  end
.
Hint Extern 1 (~ (Duality _ _)) => not_duality.

Ltac reduction_step :=
  intros; compute;
  repeat match goal with
  | [ |- Reduction _ _ (PNew (? _; _) (! _; _) ?D ?P) _ ] =>
    apply RStruct with (PNew _ _ (duality_comm D) (fun a b => P b a))
  | [ |- Reduction _ _ (PNew (&{_}) (⊕{_}) ?D ?P) _ ] =>
    apply RStruct with (PNew _ _ (duality_comm D) (fun a b => P b a))
  | [ |- Reduction _ _ (PNew _ _ ?D (fun a b => b?[m]; ?PB <|> a![?M]; ?PA)) _ ] =>
    apply RStruct with (PNew _ _ D (fun a b => a![M]; PA <|> b?[m]; PB))
  | [ |- Reduction _ _ (PNew _ _ ?D (fun a b => PBranch ?BB b ?PB <|> a◃?M; ?PA)) _ ] =>
    apply RStruct with (PNew _ _ D (fun a b => a◃M; PA <|> PBranch BB b PB))
  end;
  constructors
.
Hint Extern 1 (_ ⇒ _) => reduction_step.

Ltac big_step_reduction :=
  intros; compute; repeat (eapply RStep; reduction_step)
.
Hint Extern 1 (_ ⇒* _) => big_step_reduction.

Ltac linearity :=
  unfold Linear; simp lin in *; tauto
.
Hint Extern 1 (Linear _) => linearity.
Hint Extern 1 (~ (Linear _)) => linearity.
