Require Import Unicode.Utf8.

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
  | CCompCommutative P Q :
      PComp P Q ≡ PComp Q P

  | CCompAssociative P Q R :
      PComp (PComp P Q) R ≡ PComp P (PComp Q R)

  | CCompCongruent P Q R S :
      P ≡ Q → R ≡ S → PComp P R ≡ PComp Q S

  | CScopeExpansion s r sDr P Q R :
      (∀ (a : Message C[s]) (b : Message C[r]), P a b ≡ Q a b) →
      PComp (PNew s r sDr P) R ≡ PNew s r sDr (fun a b => PComp (Q a b) R)

  | CScopeCommutative s r sDr s' r' sDr' P Q :
      (∀ (a : Message C[s]) (b : Message C[r]) (c : Message C[s']) (d : Message C[r']), P a b c d ≡ Q a b c d) →
      PNew s r sDr (fun a b => PNew s' r' sDr' (fun c d => P a b c d)) ≡
      PNew s' r' sDr' (fun c d => PNew s r sDr (fun a b => Q a b c d))

  | CNewTypesCommutative s r sDr P Q :
      (∀ (a : Message C[s]) (b : Message C[r]), P a b ≡ Q a b) →
      PNew s r sDr (fun a b => P a b) ≡ PNew r s (inverse_duality sDr) (fun b a => Q a b)

  | CNewIrrelevant s r sDr P :
      P ≡ PNew s r sDr (fun _ _ => P)

  | CNewCongruent s r sDr P Q :
      (∀ (a : Message C[s]) (b : Message C[r]), P a b ≡  Q a b) →
      PNew s r sDr P ≡ PNew s r sDr Q

  | COutputCongruent mt (m : Message mt) st (c : Message C[! mt; st]) P Q :
      (∀ (a : Message C[st]), P a ≡ Q a) →
      POutput m P c ≡ POutput m Q c

  | CInputCongruent mt st (c : Message C[? mt; st]) P Q :
      (∀ (a : Message mt) (b : Message C[st]), P a b ≡ Q a b) →
      PInput P c ≡ PInput Q c

  | CReflective P :
      P ≡ P

  | CSymmetric P Q :
      P ≡ Q → Q ≡ P

  | CTransitive P Q R :
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
      P ≡ P' → Q ≡ Q' → P ⇒ Q → P' ⇒ Q'

  where "P ⇒ Q" := (Reduction P Q)
  .

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

(* Abstract over parametric types and their constructors *)
Definition PProcess := ∀ ST MT (mf : ∀ {S: Set}, S → Message ST MT (Base S)) , Process ST MT.
Notation "[ f ]> P" := (fun _ _ f => P)(at level 80).
Notation "P ≡ Q" := (∀ ST MT mf, Congruence _ _ (P ST MT mf) (Q ST MT mf))(at level 80).
Notation "P ⇒ Q" := (∀ ST MT mf, Reduction _ _ (P ST MT mf) (Q ST MT mf))(at level 80).

Ltac constructors :=
  repeat (intros; compute; constructor)
.


(******************************************)
(*               EXAMPLES                 *)
(******************************************)

Example example1 : PProcess :=
  [υ]> (new
    i <- (? Base bool ; ! Base bool ; ø),
    o <- (! Base bool ; ? Base bool ; ø),
    Leftwards (Rightwards Ends))

    (i?(m); !(m); ε) <|> (o!(υ _ true); ?(m); ε).

Example example2 : PProcess :=
  [υ]> (new
    o <- (! Base bool ; ? Base bool ; ø),
    i <- (? Base bool ; ! Base bool ; ø),
    Rightwards (Leftwards Ends))

    (o!(υ _ true); ?(m); ε) <|> i?(m); !(m); ε
    .

Example congruent_example : example1 ≡ example2. constructors.

Example example3 : PProcess :=
  [υ]> (new
    o <- ø,
    i <- ø,
    Ends)

    ε o <|> ε i
    .


Example reduction_example : example2 ⇒ example3. constructors.

Example nonlinear_example : PProcess :=
  [υ]> (new
    i <- (? Base bool ; ø),
    o <- (! Base bool; ø),
    (Leftwards Ends))

    (* Cheat the system by using the channel o twice *)
    i?(_); ε <|> o!(υ _ true); (fun _ => o!(υ _ true); ε)
    .

Example channel_over_channel : PProcess :=
  [υ]>
    (new i <- (? C[ ! Base bool ; ø ] ; ø), o <- (! C[ ! Base bool ; ø ] ; ø), (Leftwards Ends))
    (new i' <- (? Base bool ; ø), o' <- (! Base bool ; ø), (Leftwards Ends))

    (i?(c); fun a => ε a <|> c!(υ _ true); ε)
    <|>
    (o!(o'); fun a => ε a <|> i'?(_); ε)
.

Example channel_over_channel1 : PProcess :=
  [υ]>
    (new i' <- (? Base bool ; ø), o' <- (! Base bool ; ø), (Leftwards Ends))
    (new i <- (? C[ ! Base bool ; ø ] ; ø), o <- (! C[ ! Base bool ; ø ] ; ø), (Leftwards Ends))

    (i?(c); fun a => c!(υ _ true); ε <|> ε a)
    <|>
    (o!(o'); fun a => i'?(_); ε <|> ε a)
.

Example congruent_example : channel_over_channel ≡ channel_over_channel1. constructors.
