Require Import Unicode.Utf8.
Require Import Vectors.VectorDef.


Section Channel.
  Inductive MType : Type :=
  | Base : Set → MType 
  | Channel : CType → MType
  with CType : Type :=
  | End : CType
  | Send : MType → CType → CType
  | Receive : MType → CType → CType
  .

  Fixpoint dual (t₁ : CType) (t₂ : CType) : Prop :=
  match (t₁, t₂) with
  | (End, End) => True
  | (Send m₁ p₁, Receive m₂ p₂) => m₁ = m₂ /\ dual p₁ p₂
  | (Receive m₁ p₁, Send m₂ p₂) => m₁ = m₂ /\ dual p₁ p₂
  | _ => False
  end.

  Section Process.
    Variable channel : CType → Type.
    Variable message : MType → Type.
    
    Inductive Process : Type := 
    | PNew
      : ∀ (s r : CType)
      , (channel s → channel r → Process)
      → Process
    | PInput
      : ∀ {m : MType} {c : CType}
      , (message m → channel c → Process)
      → (channel (Receive m c))
      → Process
    | POutput
      : ∀ {m : MType} {c : CType}
      , message m
      → (channel c → Process)
      → (channel (Send m c))
      → Process
    | PComp : Process → Process → Process
    | P0 : channel End → Process
    .
  End Process.

  Implicit Arguments PNew [channel message].
  Implicit Arguments P0 [channel message].
  Implicit Arguments PInput [channel message].
  Implicit Arguments POutput [channel message].
End Channel.

Definition THRD := End.
Definition SND := Receive (Base nat) THRD.
Definition FST := Receive (Base bool) SND.

Definition minus := Send (Base bool) End.
Definition plus := Receive (Base bool) End.
Theorem meh : dual plus minus.
  simpl. auto.
Qed.
Check PNew _ _ plus minus (fun i => fun o => PComp _ _ (PInput _ _ (fun m => P0 _ _) i) (POutput _ _ _ (P0 _ _) o)).
