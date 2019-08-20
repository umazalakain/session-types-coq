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
Notation "&{ ss }" := (Branch ss) (at level 90, right associativity).
Notation "⊕{ ss }" := (Select ss) (at level 90, right associativity).

Inductive Duality : SType -> SType -> Prop :=
| Ends : Duality ø ø
| MRight : forall {m x y}, Duality x y -> Duality (Send m x) (Receive m y)
| MLeft : forall {m x y}, Duality x y -> Duality (Receive m x) (Send m y)
| SRight : forall {n} {xs ys : Vector.t SType n},
    Forall2 Duality xs ys -> Duality (Select xs) (Branch ys)
| SLeft : forall {n} {xs ys : Vector.t SType n},
    Forall2 Duality xs ys -> Duality (Branch xs) (Select ys)
.

Fixpoint inverse_duality {s r : SType} (d : Duality s r) : Duality r s :=
  (* Coq's termination checker complains if this is generalised *)
  let fix flipForall2 {n} {xs ys : Vector.t SType n}
          (ps : Forall2 Duality xs ys) : Forall2 Duality ys xs :=
      match ps with
      | Forall2_nil _ => Forall2_nil _
      | Forall2_cons _ _ _ _ _ p ps =>
        Forall2_cons _ _ _ _ _ (inverse_duality p) (flipForall2 ps)
      end
  in match d with
  | Ends => Ends
  | MRight d' => MLeft (inverse_duality d')
  | MLeft d' => MRight (inverse_duality d')
  | SRight d' => SLeft (flipForall2 d')
  | SLeft d' => SRight (flipForall2 d')
  end
.
