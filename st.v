Require Import Unicode.Utf8.
Require Import Vectors.VectorDef.

(*
ISSUES:
[ ] How to ensure linearity
[ ] How to make the duality proof compute automatically
[x] How to avoid passing channel and message to every process constructor
[x] How to send actual messages
[ ] Add pretty notation
*)

(* Represents the type of a message.
   The base type ranges over the set of all small types.
   (This should be made universe polymorphic, somehow.)
   Channels might be sent as messages.
*)
Inductive MType : Type :=
| Base : Set → MType 
| Channel : SType → MType

(* Represents session types of channels.
   Big TODO for branching and selection.
*)
with SType : Type :=
| End : SType
| Send : MType → SType → SType
| Receive : MType → SType → SType
.

(* Encode the duality of session types.
   TODO: For any two session types, their duality is decidable,
   it should therefore be computed automatically in the future.
*)
Inductive Duality : SType → SType → Prop :=
| Ends : Duality End End
| Rightwards : ∀ {m : MType} {c₁ c₂ : SType}, Duality c₁ c₂ → Duality (Send m c₁) (Receive m c₂)
| Leftwards : ∀ {m : MType} {c₁ c₂ : SType}, Duality c₁ c₂ → Duality (Receive m c₁) (Send m c₂)
.
                                                      
(* Represents the actual data over the wire.
   For some reason, going universe polymorphic with
   (A : Type) {M : A} (m : M) is not working.

   FIXME: it makes no sense to send the type of a channel.
   It is instead {S : SType} (channel s) that has to be sent.
*)
Inductive Message : MType → Type :=
| V : ∀ {M : Set}, M → Message (Base M)
| C : ∀ (C : SType), Message (Channel C)
.
  
(* Parametric HOAS representation of processes. *)
Inductive Process {channel : SType → Type} : Type := 

(* For any two dual session types,
   create their corresponding channels, and
   continue with a process where those channels are available.
*)
| PNew
  : ∀ (s r : SType)
  , Duality s r
  → (channel s → channel r → Process)
  → Process

(* Await a message m and continue with
   a process where a channel c is available,
   provided that there is a channel
   listening for a message m
   and continuing with c upon reception.
*)
| PInput
  : ∀ {m : MType} {c : SType}
  , (Message m → channel c → Process)
  → (channel (Receive m c))
  → Process

(* Send a message m and continue with
   a process where a channel c is available,
   provided that there is a channel
   sending a message m
   and continuing with c.
*)
| POutput
  : ∀ {m : MType} {c : SType}
  , Message m
  → (channel c → Process)
  → (channel (Send m c))
  → Process

(* I don't know how to represent this accurately, yet. *)
| PComp : Process → Process → Process

(* The end of all things, provided we are allowed to end. *)
| P0 : channel End → Process
.

(* Counts the instantiated variables.
   Processes are parametrised with channels represented by unit, which is always available.
   It is in this way always possible to "dive in" into processes recursively.
   The only problem are message types, which would also have to be restricted to unit.
*)
Fixpoint count_vars (p : Process (channel := fun _ => unit)) : nat :=
  match p with
  | PNew _ _ _ p => 2 + count_vars (p tt tt)
  | PInput p _ => 1 (* + count_vars (p tt tt) *)
  | POutput _ p _ => count_vars (p tt)
  | PComp p1 p2 => count_vars p1 + count_vars p2
  | P0 _ => 0
  end.

(* Transform the datatype parameter into a quantifier *)
Definition P := ∀ (c : SType → Type), Process (channel := c).

Example foo : P := fun _ => (* This process can be instantiated to whatever channel representation *)
        PNew
          (* Session types for both ends *)
          (* Pertinent notation will make this nicer to write *)
          (* NOTABLY: if you change any of this, this process won't typecheck *)
          (Receive (Base bool) End)
          (Send (Base bool) End)
          (* This is going to be computed automatically in the future *)
          (Leftwards Ends)

          (* The magic of parametric HOAS: *)
          (* i and o represent channels with pertinent session types *)
          (fun i => fun o =>
               (* Some useful typechecking should happen here *)
               PComp
                  (* Here m is the message upon arrival! *)
                  (PInput (fun m => P0) i)
                  (* We send the value 1 over the wire. *)
                  (POutput (V true) P0 o)
          ).

(* We compute the amount of variables in this process: 3! *)
Compute count_vars (foo _).
