Require Import Unicode.Utf8.
Require Import Lists.List.
Import ListNotations.
Require Import Sorting.Permutation.

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
| ø : SType
| Send : MType → SType → SType
| Receive : MType → SType → SType
.

Notation "C[ s ]" := (Channel s).
Notation "! m ; s" := (Send m s) (at level 90, right associativity). 
Notation "? m ; s" := (Receive m s) (at level 90, right associativity). 

(* Encode the duality of session types.
   TODO: For any two session types, their duality is decidable,
   it should therefore be computed automatically in the future.
*)
Inductive Duality : SType → SType → Prop :=
| Ends : Duality ø ø
| Rightwards : ∀ {m : MType} {c₁ c₂ : SType}, Duality c₁ c₂ → Duality (Send m c₁) (Receive m c₂)
| Leftwards : ∀ {m : MType} {c₁ c₂ : SType}, Duality c₁ c₂ → Duality (Receive m c₁) (Send m c₂)
.
                                                      
(* Represents the actual data over the wire.
   For some reason, going universe polymorphic with
   (A : Type) {M : A} (m : M) is not working.
*)
Inductive Message : MType → Type :=
| V : ∀ {M : Set}, M → Message (Base M)
| C : ∀ (S : SType), Message (Channel S)
.
  
(* Parametric HOAS representation of processes. *)
(* A polymorphic CT makes it impossible to produce new channels unles PNew is used *)
(* MT and f allow for all messages to be mapped into the unit type *)
(* This allows for the process to be traversed without evaluating it *)
Inductive Process {MT : Type → Type} {f : ∀ m, Message m → MT (Message m)}: Type := 

(* For any two dual session types,
   create their corresponding channels, and
   continue with a process where those channels are available.
*)
| PNew
  : ∀ (s r : SType)
  , Duality s r 
  → (MT (Message (Channel s)) → MT (Message (Channel r)) → Process)
  → Process

(* Await a message m and continue with
   a process where a channel c is available,
   provided that there is a channel
   listening for a message m
   and continuing with c upon reception.
*)
| PInput
  : ∀ {m : MType} {c : SType}
  , (MT (Message m) → MT (Message (Channel c)) → Process)
  → MT (Message (Channel (Receive m c)))
  → Process

(* Send a message m and continue with
   a process where a channel c is available,
   provided that there is a channel
   sending a message m
   and continuing with c.
*)
| POutput
  : ∀ {m : MType} {c : SType}
  , MT (Message m)
  → (MT (Message (Channel c)) → Process)
  → MT (Message (Channel (Send m c)))
  → Process

(* I don't know how to represent this accurately, yet. *)
| PComp : Process → Process → Process

(* The end of all things, provided we are allowed to end. *)
| P0 : MT (Message (Channel ø)) → Process
.

Notation "'(new' s <- S , r <- R , SdR ) p" := (PNew S R SdR (fun s r => p))(at level 90).
Notation "P <|> Q" := (PComp P Q)(at level 80).
Notation "!( m ); p" := (POutput m p)(at level 80).
Notation "c !( m ); p" := (POutput m p c)(at level 79).
Notation "?( m ); p" := (PInput (fun m => p))(at level 80).
Notation "c ?( m ); p" := (PInput (fun m => p) c)(at level 79).

Check (new s <- ø , r <- ø , Ends) P0 s <|> P0 r.

(* Transform the datatype parameter into a function *)
Definition FProcess := ∀ (MT : Type → Type) (f : ∀ m, Message m → MT (Message m)) , Process (MT := MT) (f := f). 

(* Counts the instantiated variables.
   Channels are cast into unit, which is always available.
   Message types are cast into unit, which is always available.
   It is in this way always possible to "dive in" into processes recursively.
*)
Fixpoint count_vars (p : Process (MT := fun _ => unit) (f := fun _ _ => tt)) : nat :=
  match p with
  | PNew _ _ _ p => 2 + count_vars (p tt tt)
  | PInput p _ => 1 + count_vars (p tt tt)
  | _ !( _ ); p => count_vars (p tt)
  | p1 <|> p2 => count_vars p1 + count_vars p2
  | P0 _ => 0
  end.

Fixpoint annotate (n : nat) (p : Process (MT := fun _ => nat) (f := fun _ _ => 0)) : list nat * list nat :=
  match p with
  | PNew _ _ _ p => let (created, used) := annotate (2+n) (p n (1+n))
                   in (n :: (1+n) :: created, used)
  | PInput p u => let (created, used) := annotate (1+n) (p 0 n)
                 in (n :: created, u :: used)
  | u !( _ ); p => let (created, used) := annotate (1+n) (p n)
                    in (n :: created, u :: used)
  | l <|> r => let (created, used) := annotate n l
                in let (created', used') := annotate (1 + fold_right max 0 created) r
                in (created ++ created', used ++ used')
  | P0 u  => ([], [u])
  end
.
  
Definition linear (p : FProcess) := let (created, used) := annotate 0 (p _ _)
                                    in Permutation created used.


Example linear_example : FProcess :=
  fun _ f => (new
    i <- (? Base bool ; ! Base bool ; ø),
    o <- (! Base bool ; ? Base bool ; ø),
    Leftwards (Rightwards Ends))

    (i?(m); !(m); P0) <|> (o!(f _ (V true)); ?(m); P0)
    .

(* We compute the amount of variables in this process:
   2 channels, 2 inputs, total of 4! *)
Compute count_vars (linear_example _ _).

Compute linear linear_example.

Example nonlinear_example : FProcess :=
  fun _ f => (new
    i <- (? Base bool ; ø),
    o <- (! Base bool; ø),
    (Leftwards Ends))

    (* Cheat the system by using the channel o twice *)
    (i?(_); P0) <|> (o!(f _ (V true)); (fun _ => o!(f _ (V true)); P0))
    .

Compute linear nonlinear_example.

Example channel_over_channel : FProcess :=
  fun _ f => (new
    i <- (? C[ ! Base bool ; ø ] ; ø),
    o <- (! C[ ! Base bool ; ø ] ; ø),
    (Leftwards Ends))

    (i?(c); fun a => P0 a <|> (c!(f _ (V true)); P0)) <|>
    ((new i' <- (? Base bool ; ø), o' <- (! Base bool ; ø), (Leftwards Ends))
    (o!(o'); fun a => P0 a <|> (i'?(_); P0))).

Compute linear channel_over_channel.

                               
