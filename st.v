Require Import Unicode.Utf8.
Require Import Lists.List.
Import ListNotations.
Require Import Sorting.Mergesort.

(*
ISSUES:
[ ] How to ensure linearity
[ ] How to make the duality proof compute automatically
[x] How to avoid passing channel and message to every process constructor
[x] How to send actual messages
[ ] Add pretty notation
[ ] Evaluate processes
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
*)
Inductive Message {CT : SType → Type} : MType → Type :=
| V : ∀ {M : Set}, M → Message (Base M)
| C : ∀ {S : SType}, CT S → Message (Channel S)
.
  
(* Parametric HOAS representation of processes. *)
(* A polymorphic CT makes it impossible to produce new channels unles PNew is used *)
(* MT and f allow for all messages to be mapped into the unit type *)
(* This allows for the process to be traversed without evaluating it *)
Inductive Process {CT : SType → Type} {MT : MType → MType} {f : ∀ m, Message (CT := CT) m → Message (CT := CT) (MT m)}: Type := 

(* For any two dual session types,
   create their corresponding channels, and
   continue with a process where those channels are available.
*)
| PNew
  : ∀ (s r : SType)
  , Duality s r
  → (CT s → CT r → Process)
  → Process

(* Await a message m and continue with
   a process where a channel c is available,
   provided that there is a channel
   listening for a message m
   and continuing with c upon reception.
*)
| PInput
  : ∀ {m : MType} {c : SType}
  , (Message (CT := CT) (MT m) → CT c → Process)
  → (CT (Receive m c))
  → Process

(* Send a message m and continue with
   a process where a channel c is available,
   provided that there is a channel
   sending a message m
   and continuing with c.
*)
| POutput
  : ∀ {m : MType} {c : SType}
  , Message (CT := CT) (MT m)
  → (CT c → Process)
  → (CT (Send m c))
  → Process

(* I don't know how to represent this accurately, yet. *)
| PComp : Process → Process → Process

(* The end of all things, provided we are allowed to end. *)
| P0 : CT End → Process
.

(* Transform the datatype parameter into a function *)
Definition FProcess := ∀ (CT : SType → Type) (MT : MType → MType) (f : ∀ m, Message (CT := CT) m → Message (CT := CT) (MT m)) , Process (CT := CT) (MT := MT) (f := f). 

(* Counts the instantiated variables.
   Channels are cast into unit, which is always available.
   Message types are cast into unit, which is always available.
   It is in this way always possible to "dive in" into processes recursively.
*)
Fixpoint count_vars (p : Process (CT := fun _ => unit) (MT := fun _ => Base unit) (f := fun _ _ => (V tt))) : nat :=
  match p with
  | PNew _ _ _ p => 2 + count_vars (p tt tt)
  | PInput p _ => 1 + count_vars (p (V tt) tt)
  | POutput _ p _ => count_vars (p tt)
  | PComp p1 p2 => count_vars p1 + count_vars p2
  | P0 _ => 0
  end.

Fixpoint annotate (n : nat) (p : Process (CT := fun _ => nat) (MT := fun _ => Base unit) (f := fun _ _ => (V tt))) : list nat * list nat :=
  match p with
  | PNew _ _ _ p => let (created, used) := annotate (2+n) (p n (1+n))
                   in (n :: (1+n) :: created, used)
  | PInput p u => let (created, used) := annotate (1+n) (p (V tt) n)
                 in (n :: created, u :: used)
  | POutput _ p u => let (created, used) := annotate (1+n) (p n)
                    in (n :: created, u :: used)
  | PComp l r => let (created, used) := annotate n l
                in let (created', used') := annotate (1 + fold_right max 0 created) r
                in (created ++ created', used ++ used')
  | P0 u  => ([], [u])
  end
.
  
Module Import NatSort := Sort NatOrder.

Definition linear (p : FProcess) := let (created, used) := annotate 0 (p _ _ _)
                                    in sort created = sort used.

(*
Fixpoint linearity {A : Type} (x : A) (p : Process (CT := CType → A) (MT := fun _ => Base unit) (f := fun _ _ => (V tt))) 
*)
(* How to decide linearity of processes
   ———————————————————————————————————–

   - Parametrise process by channel := fun _ => nat
     (or any other infinite set with decidable equality)
   - Keep a set of nats representing channels that have been created
   - Keep counter of natural of latest created channel
   - When going into a PNew, add new naturals and increment counter
   - When going into a send, receive or end:
     - If the channel num they are using is in the set, remove it
     - If it is not, it is not linear
*)


Example linear_example : FProcess := fun _ _ f => (* This process can be instantiated to whatever channel and message types *)
        PNew
          (* Session types for both ends *)
          (* Pertinent notation will make this nicer to write *)
          (* NOTABLY: if you change any of this, this process won't typecheck *)
          (Receive (Base bool) (Send (Base bool) End))
          (Send (Base bool) (Receive (Base bool) End))
          (* This is going to be computed automatically in the future *)
          (Leftwards (Rightwards Ends))

          (* The magic of parametric HOAS: *)
          (* i and o represent channels with pertinent session types *)
          (fun i => fun o =>
               (* Some useful typechecking should happen here *)
               PComp
                  (* Here m is the message upon arrival! *)
                  (PInput (fun m => POutput m P0) i)
                  (* We send the value 1 over the wire. *)
                  (* We use f whenever we fabricate a value
                     so that it is cast into the relevant value. *)
                  (POutput (f _ (V true)) (PInput (fun m => P0)) o)
          ).

(* We compute the amount of variables in this process:
   2 channels, 2 inputs, total of 4! *)
Compute count_vars (linear_example _ _ _).

Compute linear linear_example.

Example nonlinear_example : FProcess := fun _ _ f =>
        PNew
          (Receive (Base bool) End)
          (Send (Base bool) End)
          (Leftwards Ends)

          (fun i => fun o =>
               PComp
                  (PInput (fun _ => P0) i)
                  (* Cheat the system by using the channel o twice *)
                  (POutput (f _ (V true))
                           (fun _ => POutput (f _ (V true))
                                          P0 o) o)
          ).

Compute linear nonlinear_example.
