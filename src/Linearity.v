Require Vectors.Vector.
From Equations Require Import Equations.

Require Import Forall.
Require Import Types.
Require Import Processes.

Definition TMT : Type -> Type := fun _ => unit.
Definition fMT : forall (S: Type), S -> Message bool TMT B[S] := fun _ _ => V tt.

Definition x : forall s, Message bool TMT C[s] := fun s => C true.
Definition o : forall s, Message bool TMT C[s] := fun s => C false.
Arguments x [s].
Arguments o [s].

Derive NoConfusion for MType.
Derive Signature for Message.

Equations lin (P : Process bool TMT) : Prop := {
lin (PEnd (C true))                := False;
lin (PEnd (C false))               := True;
lin (PNew _ _ _ P)                 := lin (P o o) /\ single_x (P x o) /\ single_x (P o x);
lin (PComp P Q)                    := lin P /\ lin Q ;
lin (@PInput _    _ P (C true))    := False;
lin (@PInput B[_] _ P (C false))   := lin (P (V tt) o) /\ single_x (P (V tt) x);
lin (@PInput C[_] _ P (C false))   := lin (P o o) /\ single_x (P x o) /\ single_x (P o x);
lin (POutput _        P (C true))  := False;
lin (POutput (C true) P (C false)) := False;
lin (POutput _        P (C false)) := lin (P o) /\ single_x (P x);
lin (PSelect _ c P) with c         := {
lin (PSelect _ c P) (C true)       := False;
lin (PSelect _ c P) (C false)      := lin (P o) /\ single_x (P x)};
lin (PBranch Ps (C true))          := False;
lin (PBranch Ps (C false))         :=
  let fix branches {n} {ss : Vector.t _ n} (Ps : Forall (fun s => _ -> _) ss) :=
      match Ps with
      | Forall_nil _ => True
      | Forall_cons _ P Ps' =>
        lin (P o) /\
        single_x (P x) /\
        branches Ps'
      end
  in branches Ps

} where single_x (p : Process bool TMT) : Prop := {

single_x (PEnd (C true))                := True;
single_x (PEnd (C false))               := False;
single_x (PNew _ _ _ P)                 := single_x (P o o) ;
single_x (PComp P Q)                    := (lin P /\ single_x Q) \/ (single_x P /\ lin Q) ;
single_x (@PInput B[_] _ P (C true))    := lin (P (V tt) o) /\ single_x (P (V tt) x);
single_x (@PInput C[_] _ P (C true))    := lin (P o o) /\ single_x (P x o) /\ single_x (P o x);
single_x (@PInput B[_] _ P (C false))   := single_x (P (V tt) o) ;
single_x (@PInput C[_] _ P (C false))   := single_x (P o o);
single_x (POutput (C true) P (C true))  := False;
single_x (POutput _        P (C true))  := lin (P o) /\ single_x (P x);
single_x (POutput (C true) P (C false)) := lin (P o) /\ single_x (P x) ;
single_x (POutput _        P (C false)) := single_x (P o);
single_x (PSelect i c P) with c         := {
single_x (PSelect i c P) (C true)       := lin (P o) /\ single_x (P x) ;
single_x (PSelect i c P) (C false)      := single_x (P o)};
single_x (PBranch Ps (C m))             :=
  let fix branches {n} {ss : Vector.t _ n} (Ps : Forall (fun s => _ -> _) ss) :=
      match Ps with
      | Forall_nil _ => True
      | Forall_cons _ P Ps' =>
        (if m then lin (P o) /\ single_x (P x)
              else single_x (P o))
        /\ branches Ps'
      end
  in branches Ps
}.

Definition Linear (P : PProcess) : Prop := lin (P bool TMT fMT).
