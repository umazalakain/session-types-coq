Require Import Unicode.Utf8.
Require Import Lists.List.
Import ListNotations.
Require Import Sorting.Permutation.

(*
ISSUES:
[x] How to ensure linearity
[x] How to avoid passing channel and message to every process constructor
[x] How to send actual messages
[x] Add pretty notation
[ ] Evaluate processes
[ ] Make duality proof decidable
[ ] Make linearity decidable
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

Fixpoint inverse_duality {s r : SType} (d : Duality s r) : Duality r s :=
  match d with
  | Ends => Ends
  | Rightwards d' => Leftwards (inverse_duality d')
  | Leftwards d' => Rightwards (inverse_duality d')
  end
.
                                                                  
Section Processes.
  Variable ST : Type.
  Variable MT : Type → Type.
                                    
  Inductive Message : MType → Type :=
  | V : ∀ {M : Set}, MT M → Message (Base M)
  | C : ∀ {S : SType}, ST → Message (Channel S)
  .

  Arguments V [M].
  Arguments C [S].
  
  Inductive Process : Type := 
  
  | PNew
    : ∀ (s r : SType)
    , Duality s r 
    → (Message C[s] → Message C[r] → Process)
    → Process
  
  | PInput
    : ∀ {m : MType} {s : SType}
    , (Message m → Message C[s] → Process)
    → Message C[? m ; s]
    → Process
  
  | POutput
    : ∀ {m : MType} {s : SType}
    , Message m
    → (Message C[s] → Process)
    → Message C[! m ; s]
    → Process
  
  | PComp : Process → Process → Process
  
  | PEnd : Message C[ø] → Process
  .

  Reserved Notation "P ≡ Q" (no associativity, at level 80).
  Inductive Congruence : Process → Process → Prop :=
  | CCommutativity P Q :
      PComp P Q ≡ PComp Q P
            
  | CAssociativity P Q R :
      PComp (PComp P Q) R ≡ PComp P (PComp Q R)
            
  | CScopeExpansion s r sDr fP Q :
      PComp (PNew s r sDr fP) Q ≡ PNew s r sDr (fun a b => PComp (fP a b) Q)
            
  | CScopeCommutativity s r sDr s' r' sDr' ffP :
      PNew s r sDr (fun a b => PNew s' r' sDr' (fun c d => ffP a b c d)) ≡
      PNew s' r' sDr' (fun c d => PNew s r sDr (fun a b => ffP a b c d))
                    
  | CTypeCommutativity s r sDr fP :
      PNew s r sDr (fun a b => fP a b) ≡ PNew r s (inverse_duality sDr) (fun b a => fP a b)
           
  | CUnusedNew s r sDr P :
      P ≡ PNew s r sDr (fun _ _ => P)

  | CInnerNew s r sDr fP fQ :
      (∀ (a : Message C[s]) (b : Message C[r]), fP a b ≡  fQ a b) → PNew s r sDr fP ≡ PNew s r sDr fQ
                   
  | CInnerOutput mt (m : Message mt) st (c : Message C[! mt; st]) fP fQ :
      (∀ (a : Message C[st]), fP a ≡ fQ a) → POutput m fP c ≡ POutput m fQ c

  | CInnerLeftRed P Q R :
      P ≡ Q → PComp P R ≡ PComp Q R

  | CInnerRightRed P Q R :
      P ≡ Q → PComp R P ≡ PComp R Q
                                
  | CRefl P :
      P ≡ P

  | CSymm P Q :
      P ≡ Q → Q ≡ P

  | CTrans P Q R :
      P ≡ Q → Q ≡ R → P ≡ R

  where "P ≡ Q" := (Congruence P Q)
  .

Reserved Notation "P ⇒ Q" (at level 60).

  Inductive Reduction : Process -> Process -> Prop :=
  | RComm mt s r sDr ffP fQ : forall (m : Message mt),
      PNew (! mt; s) (? mt; r) (Rightwards sDr)
           (fun a b => PComp (POutput m fQ a) (PInput ffP b)) ⇒
      PNew s r sDr
           (fun a b => PComp (fQ a) (ffP m b))
  | RRes s r ffP ffQ :
      (∀ (a : Message C[s]) (b : Message C[r]), ffP a b ⇒ ffQ a b) →
      (∀ (sDr : Duality s r), PNew s r sDr ffP ⇒ PNew s r sDr ffQ)
      
  | RPar P Q R :
      P ⇒ Q → PComp P R ⇒ PComp Q R

  | RStruct P P' Q Q' :
      P ⇒ P' → Q ≡ Q' → P' ⇒ Q' → P ⇒ Q

  where "P ⇒ Q" := (Reduction P Q).

End Processes.

Notation "'(new' s <- S , r <- R , SdR ) p" := (PNew _ _ S R SdR (fun s r => p))(at level 90).
Notation "P <|> Q" := (PComp _ _ P Q)(at level 80).
Notation "!( m ); p" := (POutput _ _ m p)(at level 80).
Notation "c !( m ); p" := (POutput _ _ m p c)(at level 79).
Notation "?( m ); p" := (PInput _ _ (fun m => p))(at level 80).
Notation "c ?( m ); p" := (PInput _ _ (fun m => p) c)(at level 79).
Definition ε {ST : Type} {MT: Type → Type} : Message ST MT (Channel ø) → Process ST MT:= PEnd ST MT.

Arguments V [ST MT].
Arguments C [ST MT].
Arguments PNew [ST MT].
Arguments PInput [ST MT m s].
Arguments POutput [ST MT m s].
Arguments PComp [ST MT].
Arguments PEnd [ST MT].

Check (new s <- ø , r <- ø , Ends) ε s <|> ε r.
Check fun _ _ f =>
        (new s <- ! Base bool; ø , r <- ? Base bool; ø, (Rightwards Ends))
          s!(_); ε <|> r?(_); ε.

  
Definition extract {MT : Type → Type} {s : SType} {A : Type}
           (m : Message A MT C[s]) : A :=
  match m with
  | C _ n => n
  end
.
                  
Fixpoint annotate
         (n : nat)
         (p : Process nat (fun _ => unit)) : list nat * list nat :=
  let MT := fun _ => unit in
  match p with

  (* Create two new channels *)
  (* No channels are used *)
  | PNew _ _ _ p =>
    let (created, used) := annotate (2+n) (p (C _ n) (C _ (1+n))) in
    (n :: 1+n :: created, used)

  | @PInput _ _ m s p c =>
    (match m as m' return (Message nat MT m' →
                          Message nat MT (Channel s) →
                          Process nat MT) →
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

  | POutput m p c =>
    (* Create a channel for the subsequent process *)
    (* Use the channel that is being outputed *)
    (* Use the channel of the parent process *)
    let (created, used) := annotate (1+n) (p (C _ n)) in
    match m with
    | V _ _ => (n :: created, extract c :: used)
    | C _ mc => (n :: created, mc :: extract c :: used)
    end

  | PComp l r  =>
    let (created, used) := annotate n l in
    let (created', used') := annotate (1 + fold_right max (n-1) created) r in
    (created ++ created', used ++ used')

  | PEnd c => ([], [extract c])
  end
.

(* Make this into a type *)
Definition FProcess := ∀ ST MT (bf : ∀ {S: Set}, S → Message ST MT (Base S)) , Process ST MT.
Notation "P ≡ Q" := (∀ ST MT f, Congruence _ _ (P ST MT f) (Q ST MT f))(at level 80).
Notation "P ⇒ Q" := (∀ ST MT f, Reduction _ _ (P ST MT f) (Q ST MT f))(at level 80).

Definition Linear (p : FProcess) := let (created, used) := annotate 0 (p _ _ (fun _ _ => V _ tt))
                                    in Permutation created used.

Example linear_example : FProcess :=
  fun ST MT f => (new
    i <- (? Base bool ; ! Base bool ; ø),
    o <- (! Base bool ; ? Base bool ; ø),
    Leftwards (Rightwards Ends))

    (i?(m); !(m); ε) <|> (o!(f _ true); ?(m); ε)
    .

Compute Linear linear_example.

Example linear_example2 : FProcess :=
  fun ST MT f => (new
    o <- (! Base bool ; ? Base bool ; ø),
    i <- (? Base bool ; ! Base bool ; ø),
    Rightwards (Leftwards Ends))

    (o!(f _ true); ?(m); ε) <|> i?(m); !(m); ε
    .

Example congruent_example : linear_example ≡ linear_example2.
  Proof.
    intros.
    compute.
    constructor 13 with ((newo <- ! Base bool; ? Base bool; ø, i <- ? Base bool; ! Base bool; ø,
    Rightwards (Leftwards Ends)) i ?( m ); (!( m ); PEnd (MT:=MT)) <|>  o !( f bool true ); (?( _ ); PEnd (MT:=MT))).
    constructor 5.
    constructor 7.
    intros.
    constructor 1.
  Qed.
                                  
Example nonlinear_example : FProcess :=
  fun _ _ f => (new
    i <- (? Base bool ; ø),
    o <- (! Base bool; ø),
    (Leftwards Ends))

    (* Cheat the system by using the channel o twice *)
    i?(_); ε <|> o!(f _ true); (fun _ => o!(f _ true); ε)
    .

Compute Linear nonlinear_example.

Example channel_over_channel : FProcess :=
  fun _ _ f =>
    (new i <- (? C[ ! Base bool ; ø ] ; ø), o <- (! C[ ! Base bool ; ø ] ; ø), (Leftwards Ends))
    (new i' <- (? Base bool ; ø), o' <- (! Base bool ; ø), (Leftwards Ends))

    (i?(c); fun a => ε a <|> c!(f _ true); ε)
    <|>
    (o!(o'); fun a => ε a <|> i'?(_); ε)
.

Compute Linear channel_over_channel.
