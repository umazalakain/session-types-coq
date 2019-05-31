Require Import Unicode.Utf8.
Require Import Vectors.VectorDef.

(*
ISSUES:
[ ] How to ensure linearity
[ ] How to make the duality proof compute automatically
[x] How to avoid passing channel and message to every process constructor
[x] How to send actual messages
*)

Inductive MType : Type :=
| Base : Set → MType 
| Channel : CType → MType
with CType : Type :=
| End : CType
| Send : MType → CType → CType
| Receive : MType → CType → CType
.

Inductive Duality : CType → CType → Prop :=
| Ends : Duality End End
| Rightwards : ∀ {m : MType} {c₁ c₂ : CType}, Duality c₁ c₂ → Duality (Send m c₁) (Receive m c₂)
| Leftwards : ∀ {m : MType} {c₁ c₂ : CType}, Duality c₁ c₂ → Duality (Receive m c₁) (Send m c₂)
.
                                                      
Inductive Message : MType → Type :=
| V : ∀ {M : Set}, M → Message (Base M)
| C : ∀ (C : CType), Message (Channel C)
.
  
Inductive Process {channel : CType → Type} : Type := 
| PNew
  : ∀ (s r : CType)
  , Duality s r
  → (channel s → channel r → Process)
  → Process
| PInput
  : ∀ {m : MType} {c : CType}
  , (Message m → channel c → Process)
  → (channel (Receive m c))
  → Process
| POutput
  : ∀ {m : MType} {c : CType}
  , Message m
  → (channel c → Process)
  → (channel (Send m c))
  → Process
| PComp : Process → Process → Process
| P0 : channel End → Process
.

Definition minus := Send (Base bool) End.
Definition plus := Receive (Base bool) End.

Definition meh : Process (channel := fun _ => unit) := PNew plus minus (Leftwards Ends) (fun i => fun o => PComp (PInput (fun m => P0) i) (POutput (V true) P0 o)).
Print meh.
