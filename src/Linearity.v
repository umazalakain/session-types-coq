Require Vectors.Vector.
From Equations Require Import Equations.

Require Import Forall.
Require Import Types.
Require Import Processes.

Definition TMT : Type -> Type := fun _ => unit.
Definition fMT : forall (S: Type), S -> Message bool TMT B[S] := fun _ _ => V tt.

Definition marked : forall s, Message bool TMT C[s] := fun s => C true.
Definition unmarked : forall s, Message bool TMT C[s] := fun s => C false.
Arguments marked [s].
Arguments unmarked [s].

(* Always recurse by passing unmarked arguments.
   If the constructor accepts a channel as an argument, it has been used.
   If a channel is sent as output, it has been used.
   Channels received as input are considered fresh.
*)

Derive NoConfusion for MType.
Derive Signature for Message.

Equations linear (P : Process bool TMT) : Prop := {
linear (PNew _ _ _ P) =>
  single_marked (P marked unmarked) /\
  single_marked (P unmarked marked) /\
  linear (P unmarked unmarked) ;
linear (@PInput m _ P c) with c => {
| (C true) => False ;
| (C false) with m => {
  | B[_] =>
    single_marked (P (V tt) marked) /\
    linear (P (V tt) unmarked) ;
  | C[_] =>
    single_marked (P marked unmarked) /\
    single_marked (P unmarked marked) /\
    linear (P unmarked unmarked)}};
linear (POutput m P c) with c => {
| (C true) => False ;
| (C false) with m => {
  | (C true) => False ;
  | _ =>
    single_marked (P marked) /\
    linear (P unmarked)}};
linear (PComp P Q) => linear P /\ linear Q ;
linear (PEnd c) with c => {
| (C true) => False ;
| (C false) => True};
linear (PSelect _ c P) with c => {
| (C true) => False ;
| (C false) =>
  single_marked (P marked) /\
  linear (P unmarked)};
linear (PBranch Ps c) with c => {
| (C true) => False ;
| (C false) =>
  let fix branches {n} {ss : Vector.t _ n} (Ps : Forall (fun s => _ -> _) ss) :=
      match Ps with
      | Forall_nil _ => True
      | Forall_cons _ P Ps' =>
        linear (P unmarked) /\
        single_marked (P marked) /\
        branches Ps'
      end
  in branches Ps}

} where single_marked (p : Process bool TMT) : Prop := {

single_marked (PNew _ _ _ P) => single_marked (P unmarked unmarked) ;
single_marked (@PInput m _ P c) with c => {
| (C true) with m => {
  | B[_] =>
    linear (P (V tt) unmarked) /\
    single_marked (P (V tt) marked);
  | C[_] =>
    linear (P unmarked unmarked) /\
    single_marked (P marked unmarked) /\
    single_marked (P unmarked marked)};
| (C false) with m => {
  | B[_] => single_marked (P (V tt) unmarked) ;
  | C[_] => single_marked (P unmarked unmarked)}};
single_marked (POutput m P c) with c => {
| (C true) with m => {
  | (C true) => False ;
  | _ => linear (P unmarked) /\ single_marked (P marked)};
| (C false) with m => {
  | (C true) => linear (P unmarked) /\ single_marked (P marked) ;
  | _ => single_marked (P unmarked)}};
single_marked (PComp P Q) =>
  (linear P /\ single_marked Q) \/
  (single_marked P /\ linear Q) ;
single_marked (PEnd c) with c => {
| (C true) => True;
| (C false) => False};
single_marked (PSelect i c P) with c => {
| (C true) => linear (P unmarked) /\ single_marked (P marked) ;
| (C false) => single_marked (P unmarked)};
single_marked (PBranch Ps c) with c => {
| (C true) =>
  let fix branches {n} {ss : Vector.t _ n} (Ps : Forall (fun s => _ -> _) ss) :=
      match Ps with
      | Forall_nil _ => True
      | Forall_cons _ P Ps' =>
        linear (P unmarked) /\
        single_marked (P marked) /\
        branches Ps'
      end
  in branches Ps ;
| (C false) =>
  let fix branches {n} {ss : Vector.t _ n} (Ps : Forall (fun s => _ -> _) ss) :=
      match Ps with
      | Forall_nil _ => True
      | Forall_cons _ P Ps' =>
        single_marked (P unmarked) /\
        branches Ps'
      end
  in branches Ps
}}.
