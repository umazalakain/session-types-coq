Require Import Forall.
Require Vectors.Vector.

Inductive MType : Type :=
| Base : Type -> MType
| Channel : SType -> MType

with SType : Type :=
| ø : SType
| Send : MType -> SType -> SType
| Receive : MType -> SType -> SType
| Branch: forall {n}, Vector.t SType n -> SType
| Select : forall {n}, Vector.t SType n -> SType
.

Notation "B[ s ]" := (Base s).
Notation "C[ s ]" := (Channel s).
Notation "! m ; s" := (Send m s) (at level 90, right associativity).
Notation "? m ; s" := (Receive m s) (at level 90, right associativity).
Notation "&{ ss }" := (Branch ss) (at level 5, right associativity).
Notation "⊕{ ss }" := (Select ss) (at level 5, right associativity).

Inductive Duality : SType -> SType -> Prop :=
| Ends : Duality ø ø
| MRight : forall {m x y}, Duality x y -> Duality (! m; x) (? m; y)
| MLeft : forall {m x y}, Duality x y -> Duality (? m; x) (! m; y)
| SRight : forall {n} {xs ys : Vector.t SType n},
    Forall2 Duality xs ys -> Duality ⊕{xs} &{ys}
| SLeft : forall {n} {xs ys : Vector.t SType n},
    Forall2 Duality xs ys -> Duality &{xs} ⊕{ys}
.

Fixpoint duality_comm {s r : SType} (d : Duality s r) : Duality r s :=
  (* Coq's termination checker complains if this is generalised *)
  let fix flipForall2 {n} {xs ys : Vector.t SType n}
          (ps : Forall2 Duality xs ys) : Forall2 Duality ys xs :=
      match ps with
      | Forall2_nil _ => Forall2_nil _
      | Forall2_cons _ _ _ _ _ p ps =>
        Forall2_cons _ _ _ _ _ (duality_comm p) (flipForall2 ps)
      end
  in match d with
  | Ends => Ends
  | MRight d' => MLeft (duality_comm d')
  | MLeft d' => MRight (duality_comm d')
  | SRight d' => SLeft (flipForall2 d')
  | SLeft d' => SRight (flipForall2 d')
  end
.
