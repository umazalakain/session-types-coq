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
                                                      
Section Processes.
  Variable ST : SType → Type.
  Variable MT : Type → Type.
                                    
  (* Represents the actual data over the wire.
     For some reason, going universe polymorphic with
     (A : Type) {M : A} (m : M) is not working.
  *)
  
  Inductive Message : MType → Type :=
  | V : ∀ {M : Set}, MT M → Message (Base M)
  | C : ∀ {S : SType}, ST S → Message (Channel S)
  .
  
  Inductive Process : Type := 
  
  (* For any two dual session types,
     create their corresponding channels, and
     continue with a process where those channels are available.
  *)
  | PNew
    : ∀ (s r : SType)
    , Duality s r 
    → (Message (Channel s) → Message (Channel r) → Process)
    → Process
  
  (* Await a message m and continue with
     a process where a channel c is available,
     provided that there is a channel
     listening for a message m
     and continuing with c upon reception.
  *)
  | PInput
    : ∀ {m : MType} {c : SType}
    , (Message m → Message (Channel c) → Process)
    → Message (Channel (Receive m c))
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
    → (Message (Channel c) → Process)
    → Message (Channel (Send m c))
    → Process
  
  (* I don't know how to represent this accurately, yet. *)
  | PComp : Process → Process → Process
  
  (* The end of all things, provided we are allowed to end. *)
  | PEnd : Message (Channel ø) → Process
  .
End Processes.

Notation "'(new' s <- S , r <- R , SdR ) p" := (PNew _ _ S R SdR (fun s r => p))(at level 90).
Notation "P <|> Q" := (PComp _ _ P Q)(at level 80).
Notation "!( m ); p" := (POutput _ _ m p)(at level 80).
Notation "c !( m ); p" := (POutput _ _ m p c)(at level 79).
Notation "?( m ); p" := (PInput _ _ (fun m => p))(at level 80).
Notation "c ?( m ); p" := (PInput _ _ (fun m => p) c)(at level 79).
Definition ε {ST : SType → Type} {MT: Type → Type} : Message ST MT (Channel ø) → Process ST MT:= PEnd ST MT.

Arguments V [ST MT].
Arguments C [ST MT].
Arguments PNew [ST MT].
Arguments PInput [ST MT].
Arguments POutput [ST MT].
Arguments PComp [ST MT].
Arguments PEnd [ST MT].

Check (new s <- ø , r <- ø , Ends) ε s <|> ε r.
Check fun _ _ f =>
        (new s <- ! Base bool; ø , r <- ? Base bool; ø, (Rightwards Ends))
          s!(_); ε <|> r?(_); ε.

  
(* Make this into a type *)
Definition FProcess := ∀ ST MT (bf : ∀ {S: Type}, S → MT S) , Process ST MT.

Definition extract {MT : Type → Type} {s : SType}
           (m : Message (fun _ => nat) MT (Channel s)) : nat :=
  match m with
  | C _ n => n
  end
.
                  
Fixpoint annotate
         (n : nat)
         (p : Process (fun _ => nat) (fun _ => unit)) : list nat * list nat :=
  let ST := fun _ => nat in
  let MT := fun _ => unit in
  match p with

  (* Create two new channels *)
  (* No channels are used *)
  | PNew _ _ _ p =>
    let (created, used) := annotate (2+n) (p (C _ n) (C _ (1+n))) in
    (n :: 1+n :: created, used)

  | @PInput _ _ m s p c =>
    (match m as m' return (Message ST MT m' →
                          Message ST MT (Channel s) →
                          Process ST MT) →
                          list nat * list nat
     with
     (* A base value is received over the wire *)
     (* Create a channel for the subsequent process *)
     (* Use the channel of the parent process *)
     | Base _ => fun p' =>
       let (created, used) := annotate (1+n) (p' (V _ tt) (C _ n)) in
       (n :: created, extract c :: used)

     (* A channel is received over the wire *)
     (* Create a channel for the subsequent process *)
     (* Create a channel for the received message *)
     (* Use the channel of the parent process *)
     | Channel _ => fun p' =>
       let (created, used) := annotate (2+n) (p' (C _ n) (C _ (1+n))) in
       (n :: 1+n :: created, extract c :: used)
     end) p

  | POutput _ _ m p c =>
    (* Create a channel for the subsequent process *)
    let (created, used) := annotate (1+n) (p (C _ n)) in
    match m with
    | V _ _ => (n :: created, extract c :: used)
    | C _ mc => (mc :: n :: created, extract c :: used)
    end

  | l <|> r  =>
    let (created, used) := annotate n l in
    let (created', used') := annotate (1 + fold_right max 0 created) r in
    (created ++ created', used ++ used')

  | PEnd c => ([], [extract c])
  end
.

  
Definition linear (p : FProcess) := let (created, used) := annotate 0 (p _ _ (fun _ _ => tt))
                                    in Permutation created used.


Example linear_example : FProcess :=
  fun ST MT f => (new
    i <- (? Base bool ; ! Base bool ; ø),
    o <- (! Base bool ; ? Base bool ; ø),
    Leftwards (Rightwards Ends))

    (i?(m); !(m); ε) <|> (o!(V _ (f _ true)); ?(m); ε)
    .

Compute linear linear_example.

Example nonlinear_example : FProcess :=
  fun _ _ f => (new
    i <- (? Base bool ; ø),
    o <- (! Base bool; ø),
    (Leftwards Ends))

    (* Cheat the system by using the channel o twice *)
    i?(_); ε <|> o!(V _ (f _ true)); (fun _ => o!(V _ (f _ true)); ε)
    .

Compute linear nonlinear_example.

Example channel_over_channel : FProcess :=
  fun _ _ f => (new
    i <- (? C[ ! Base bool ; ø ] ; ø),
    o <- (! C[ ! Base bool ; ø ] ; ø),
    (Leftwards Ends))

    (i?(c); fun a => ε a <|> (c!(V _ (f _ true)); ε)) <|>
    ((new i' <- (? Base bool ; ø), o' <- (! Base bool ; ø), (Leftwards Ends))
    (o!(o'); fun a => ε a <|> (i'?(_); ε))).

Compute linear channel_over_channel.

                               
