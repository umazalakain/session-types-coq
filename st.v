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
[x] Add pretty notation
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

Inductive Message {ST : SType → Type} {MT : Set → Type} : MType → Type :=
| V : ∀ {M : Set}, MT M → Message (Base M)
| C : ∀ {S : SType}, ST S → Message (Channel S)
.

Inductive Process {ST : SType → Type} {MT : Set → Type} : Type := 

(* For any two dual session types,
   create their corresponding channels, and
   continue with a process where those channels are available.
*)
| PNew
  : ∀ (s r : SType)
  , Duality s r 
  → ( Message (ST := ST) (MT := MT) (Channel s)
    → Message (ST := ST) (MT := MT) (Channel r)
    → Process)
  → Process

(* Await a message m and continue with
   a process where a channel c is available,
   provided that there is a channel
   listening for a message m
   and continuing with c upon reception.
*)
| PInput
  : ∀ {m : MType} {c : SType}
  , ( Message (ST := ST) (MT := MT) m
    → Message (ST := ST) (MT := MT) (Channel c)
    → Process)
  → Message (ST := ST) (MT := MT) (Channel (Receive m c))
  → Process

(* Send a message m and continue with
   a process where a channel c is available,
   provided that there is a channel
   sending a message m
   and continuing with c.
*)
| POutput
  : ∀ {m : MType} {c : SType}
  , Message (ST := ST) (MT := MT) m
  → (Message (ST := ST) (MT := MT) (Channel c) → Process)
  → Message (ST := ST) (MT := MT) (Channel (Send m c))
  → Process

(* I don't know how to represent this accurately, yet. *)
| PComp : Process → Process → Process

(* The end of all things, provided we are allowed to end. *)
| P0 : Message (ST := ST) (MT := MT) (Channel ø) → Process
.

Notation "'(new' s <- S , r <- R , SdR ) p" := (PNew S R SdR (fun s r => p))(at level 90).
Notation "P <|> Q" := (PComp P Q)(at level 80).
Notation "!( m ); p" := (POutput m p)(at level 80).
Notation "c !( m ); p" := (POutput m p c)(at level 79).
Notation "?( m ); p" := (PInput (fun m => p))(at level 80).
Notation "c ?( m ); p" := (PInput (fun m => p) c)(at level 79).

Check (new s <- ø , r <- ø , Ends) P0 s <|> P0 r.

(* Transform the datatype parameters into a type *)
Definition FProcess := ∀ (ST : SType → Type) (MT : Set → Type), Process (ST := ST) (MT := MT).

Definition extract {MT : Set → Set} {s : SType}
           (m : Message (ST := fun _ => nat) (MT := MT) (Channel s)) : nat :=
  match m with
    | C n => n
  end
.
                  
Fixpoint annotate
         (n : nat)
         (p : Process (ST := fun _ => nat) (MT := fun _ => unit)) : list nat * list nat :=
  let ST := fun _ => nat in
  let MT := fun _ => unit in
  match p with

  | PNew _ _ _ p =>
    let (created, used) := annotate (2+n) (p (C n) (C (1+n))) in
    (n :: 1+n :: created, used)

  | @PInput _ _ m s p c =>
    (match m as m' return (Message (ST := ST) (MT := MT) m' →
                          Message (ST := ST) (MT := MT) (Channel s) →
                          Process (ST := ST) (MT := MT)) →
                          list nat * list nat
     with
     | Base _ => fun p' =>
       let (created, used) := annotate (1+n) (p' (V tt) (C n)) in
       (n :: created, used)
     | Channel _ => fun p' =>
       let (created, used) := annotate (2+n) (p' (C n) (C (1+n))) in
       (n :: 1+n :: created, used)
     end) p

  | POutput m p c => ([], [])

  | l <|> r => let (created, used) := annotate n l
                in let (created', used') := annotate (1 + fold_right max 0 created) r
                in (created ++ created', used ++ used')
  | P0 c => ([], [extract c])
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

                               
