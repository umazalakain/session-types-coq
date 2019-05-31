Require Import Unicode.Utf8.
Require Import Vectors.VectorDef.

(*
ISSUES:
- How to ensure linearity
- How to make the duality proof compute automatically
- How to avoid passing channel and message to every process constructor
*)

Section Channel.
  Inductive MType : Type :=
  | Base : Set → MType 
  | Channel : CType → MType
  with CType : Type :=
  | End : CType
  | Send : MType → CType → CType
  | Receive : MType → CType → CType
  .

  Fixpoint dual (t₁ t₂ : CType) : Prop :=
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
      , dual s r  
      → (channel s → channel r → Process)
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
End Channel.

Definition P := ∀ (T : CType → Type) (M : MType → Type), Process T M.
Definition P1 (s : CType) := ∀ (T : CType → Type) (M : MType → Type), T s.
Definition P2 (s r : CType) := ∀ (T : CType → Type) (M : MType → Type), T s → T r → Process T M.
Definition N (s r : CType) (d : dual s r) (p : P2 s r) : P := fun _ _ => PNew _ _ s r d (p _ _).
Definition Z (p : P1 End) : P := fun C M => P0 C M (p C M).
Check N End End I (fun _ _ c => Z).               
                                                
Check =?.
Definition minus := Send (Base bool) End.
Definition plus := Receive (Base bool) End.
Theorem meh : dual plus minus.
  simpl. auto.
Qed.
Check PNew _ _ plus minus I (fun i => fun o => PComp _ _ (PInput _ _ (fun m => P0 _ _) i) (POutput _ _ _ (P0 _ _) o)).
