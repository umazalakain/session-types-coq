Require Import Unicode.Utf8.
Require Import Lists.List.
Require Import Sorting.Permutation.
Require Import Coq.Program.Equality.
Require Import Arith.

(*
ISSUES:
- Mix congruence and reduction in a tactic.
- Include linearity in the definition of well-typedness.
*)

Inductive MType : Type :=
| Base : Set → MType
| Channel : SType → MType

with SType : Type :=
| ø : SType
| Send : MType → SType → SType
| Receive : MType → SType → SType
.

Notation "C[ s ]" := (Channel s).
Notation "! m ; s" := (Send m s) (at level 90, right associativity).
Notation "? m ; s" := (Receive m s) (at level 90, right associativity).

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

Transparent inverse_duality.
Hint Unfold inverse_duality.

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
  | RComm mt s r sDr P Q : forall (m : Message mt),
      PNew (! mt; s) (? mt; r) (Rightwards sDr)
           (fun a b => PComp (POutput m Q a) (PInput P b)) ⇒
      PNew s r sDr
           (fun a b => PComp (Q a) (P m b))

  | RRes s r P Q :
      (∀ (a : Message C[s]) (b : Message C[r]), P a b ⇒ Q a b) →
      (∀ (sDr : Duality s r), PNew s r sDr P ⇒ PNew s r sDr Q)

  | RPar P Q R :
      P ⇒ Q → PComp P R ⇒ PComp Q R

  | RStruct P Q R :
      P ≡ Q → Q ⇒ R → P ⇒ R

  where "P ⇒ Q" := (Reduction P Q)
  .

  Reserved Notation "P ⇒⇒ Q" (at level 60).
  Inductive BigStepReduction : Process → Process → Prop :=
  | RSmall P Q : P ⇒ Q → P ⇒⇒ Q
  | RTrans P Q R : P ⇒⇒ Q → Q ⇒⇒ R → P ⇒⇒ R
  | RRefl P : P ⇒⇒ P
  where "P ⇒⇒ Q" := (BigStepReduction P Q)
  .
End Processes.

(**************************)
(*        NICETIES        *)
(**************************)

Notation "'(new' s <- S , r <- R , SdR ) p" := (PNew _ _ S R SdR (fun s r => p))(at level 90).
Notation "P <|> Q" := (PComp _ _ P Q)(at level 80).
Notation "!( m ); p" := (POutput _ _ m p)(at level 80).
Notation "c !( m ); p" := (POutput _ _ m p c)(at level 79).
Notation "?( m ); p" := (PInput _ _ (fun m => p))(at level 80).
Notation "c ?( m ); p" := (PInput _ _ (fun m => p) c)(at level 79).
Definition ε {ST : Type} {MT: Type → Type} : Message ST MT (Channel ø) → Process ST MT:= PEnd ST MT.

Arguments V [ST MT M].
Arguments C [ST MT S].
Arguments PNew [ST MT].
Arguments PInput [ST MT m s].
Arguments POutput [ST MT m s].
Arguments PComp [ST MT].
Arguments PEnd [ST MT].

(**************************)
(*       LINEARITY        *)
(**************************)

Definition is_marked {MT : Type → Type} {s : SType} {A : Type}
           (m : Message A MT C[s]) : A :=
  match m with
  | C n => n
  end
.
Notation "'count_if_marked' c" := (if is_marked c then 1 else 0)(at level 50).
Definition marked : ∀ s, Message bool (fun _ => unit) C[s] := fun s => C true.
Definition unmarked : ∀ s, Message bool (fun _ => unit) C[s] := fun s => C false.
Arguments marked [s].
Arguments unmarked [s].

(* Always recurse by passing unmarked arguments.
   If the constructor accepts a channel as an argument, it has been used.
   If a channel is sent as output, it has been used.
   Channels received as input are considered fresh.
*)

Fixpoint count_marked (p : Process bool (fun _ => unit)) : nat :=
  let MT := fun _ => unit in
  match p with
  | PNew _ _ _ p => count_marked (p unmarked unmarked)

  | @PInput _ _ mt s p c =>
    count_if_marked c +
    (match mt as mt'
           return (Message bool MT mt' → Message bool MT (Channel s) → Process bool MT) → nat
     with
     | Base _ => fun p' => count_marked (p' (V tt) unmarked)
     | Channel _ => fun p' => count_marked (p' unmarked unmarked)
     end) p

  | @POutput _ _ mt s m p c =>
    count_if_marked c + count_marked (p unmarked) +
    (match mt as mt' return (Message bool MT mt') → nat with
     | Base _ => fun m' => 0
     | Channel _ => fun m' => count_if_marked m'
     end) m

  | PComp l r  => count_marked l + count_marked r

  | PEnd c => count_if_marked c
  end
.

Notation "'single_marked' p" := (count_marked p = 1)(at level 50).

Fixpoint linear (p : Process bool (fun _ => unit)) : Prop :=
  let MT := fun _ => unit in
  match p with
  | PNew _ _ _ p =>
    single_marked (p marked unmarked) /\
    single_marked (p unmarked marked) /\
    linear (p unmarked unmarked)

  | @PInput _ _ mt s p c =>
    is_marked c = false /\
    (match mt as mt'
           return (Message bool MT mt' → Message bool MT (Channel s) → Process bool MT) → Prop
     with
     | Base _ => fun p' =>
                  single_marked (p' (V tt) marked) /\
                  linear (p' (V tt) unmarked)
     | Channel _ => fun p' =>
                     single_marked (p' marked unmarked) /\
                     single_marked (p' unmarked marked) /\
                     linear (p' unmarked unmarked)
     end) p

  | @POutput _ _ mt s m p c =>
    is_marked c = false /\
    single_marked (p marked) /\
    linear (p unmarked) /\
    (match mt as mt' return (Message bool MT mt') → Prop with
     | Base _ => fun m' => True
     | Channel _ => fun m' => is_marked m' = false
     end) m

  | PComp l r => linear l /\ linear r

  | PEnd c => is_marked c = false
  end
.

(******************************)
(*  PARAMETRIC GENERALISATION *)
(******************************)

(* Abstract over parametric types and their constructors *)
Definition PProcess := ∀ ST MT (mf : ∀ {S: Set}, S → Message ST MT (Base S)) , Process ST MT.
Definition Linear (p : PProcess) : Prop := linear (p bool (fun _ => unit) (fun _ _ => (V tt))).
Notation "[ f ]> P" := (fun _ _ f => P)(at level 80).
Notation "P ≡ Q" := (∀ ST MT mf, Congruence _ _ (P ST MT mf) (Q ST MT mf))(at level 80).
Notation "P ⇒ Q" := (∀ ST MT mf, Reduction _ _ (P ST MT mf) (Q ST MT mf))(at level 80).
Notation "P ⇒⇒ Q" := (∀ ST MT mf, BigStepReduction _ _ (P ST MT mf) (Q ST MT mf))(at level 80).

(*********************************)
(*      REDUCTION TACTICS        *)
(*********************************)

Ltac constructors :=
  repeat (intros; compute; constructor)
.

Ltac reduction_step :=
  intros; compute;
  repeat match goal with
  | [ |- Reduction _ _ (PNew (? _; _) (! _; _) ?D ?P) _ ] =>
    apply RStruct with (PNew _ _ (inverse_duality D) (fun a b => P b a))
  | [ |- Reduction _ _ (PNew _ _ ?D (fun a b => b?(m); ?PB <|> a!(?M); ?PA)) _ ] =>
    apply RStruct with (PNew _ _ D (fun a b => a!(M); PA <|> b?(m); PB))
  end;
  constructors
.

Ltac big_step_reduction :=
  repeat intros; compute; eapply RTrans; eapply RSmall; try reduction_step
.

Ltac destruct_linear :=
  repeat
  match goal with
  | [ H : linear _ |- _ ] => destruct H
  end;
  repeat
  match goal with
  | [ H : and _ _ |- _ ] => destruct H
  end
.


(******************************************)
(*          TYPE PRESERVATION             *)
(******************************************)

Lemma linearity_count : ∀ P, linear P → count_marked P = 0.
Proof.
  intros P lP.
  induction P.
  all: simpl; eauto.
  + destruct_linear.
    eauto.
  + dependent induction m.
    dependent induction m0.
    all: destruct_linear; rewrite H0; eauto.
  + dependent induction m.
    dependent induction m0.
    all: destruct_linear; rewrite H0; rewrite (H _).
    all: try rewrite H3; eauto.
  + destruct_linear.
    rewrite (IHP1 H).
    rewrite (IHP2 H0).
    reflexivity.
  + dependent induction m.
    induction s.
    discriminate.
    trivial.
Qed.

Hint Resolve linearity_count.

Lemma congruence_count : ∀ P Q, Congruence _ _ P Q → count_marked P = count_marked Q.
Proof.
  intros P Q PcQ.
  induction PcQ.
  all: simpl; eauto; try ring.
  - induction mt; eauto.
  - rewrite IHPcQ1. rewrite IHPcQ2. reflexivity.
Qed.

Hint Resolve congruence_count.

Theorem linearity_congruence : ∀ P Q, Congruence _ _ P Q → linear P → linear Q.
Proof.
  intros P Q PcQ lP.
  induction PcQ.
  all: simpl; destruct_linear; eauto.
  + repeat rewrite <- (congruence_count _ _ (H _ _)).
    rewrite (linearity_count _ H2).
    rewrite H1.
    rewrite H3.
    eauto.
  + repeat rewrite <- (congruence_count _ _ (H _ _ _ _)).
    destruct_linear.
    all: try split; eauto.
  + repeat rewrite <- (congruence_count _ _ (H _ _)).
    all: eauto.
  + repeat rewrite <- (congruence_count _ _ (H _ _)).
    all: eauto.
  + dependent induction mt.
    all: rewrite <- (congruence_count _ _ (H _)).
    all: eauto.
  + dependent induction mt.
    all: repeat rewrite <- (congruence_count _ _ (H _ _)).
    all: destruct_linear; eauto.
  + admit.
Admitted.


Lemma mark_count : ∀ s (P : Message _ _ C[s] → Process _ _) (m : Message bool _ C[s]),
    count_marked (P m) = (count_if_marked m) + count_marked (P unmarked).
Proof.
Admitted.

Lemma reduction_count : ∀ P Q, Reduction _ _ P Q → count_marked P = count_marked Q.
Proof.
  intros P Q PrQ.
  induction PrQ.
  all: simpl; eauto.
  - dependent induction m.
    destruct m.
    eauto.
    rewrite (mark_count _ (fun c => P c unmarked) (C s0)).
    ring.
  - rewrite <- IHPrQ.
    apply (congruence_count _ _ H).
Qed.

Hint Resolve reduction_count.

Theorem TypePreservation : ∀ (P Q : PProcess), Linear P → P ⇒ Q → Linear Q.
Proof.
  intros P Q lP PrQ.
  unfold PProcess in P, Q.
  unfold Linear.
  unfold Linear in lP.
  set (ST := bool).
  set (MT := fun _ => unit).
  set (fM := fun _ _ => V tt).
  refine (
      (match (P ST MT fM) as P'
             return linear P' → Reduction _ _ P' (Q ST MT fM) → linear (Q ST MT fM)
       with
       | _ => _
       end) lP (PrQ ST MT fM)).
  all: intros slP sPrQ.
  induction (sPrQ).
  all: simpl.
  - destruct_linear.
    dependent induction m.
    rewrite <- (linearity_count _ H1).
    destruct (mark_count _ Q0 marked).
    admit.
    admit.
  - destruct_linear.
    repeat rewrite <- (reduction_count _ _ (H _ _)).
    eauto.
  - destruct_linear.
    eauto.
  - exact (IHr (linearity_congruence _ _ H slP) r).
Admitted.

(******************************************)
(*               EXAMPLES                 *)
(******************************************)

Example example1 : PProcess.
  refine
  ([υ]> (new i <- _, o <- _, _)
    (i?(m); !(m); ε) <|> (o!(υ _ true); ?(m); ε)).
  constructors.
Defined.
Print example1.

Example example2 : PProcess.
  refine
  ([υ]> (new o <- (! Base bool ; ? Base bool ; ø), i <- (? Base bool ; ! Base bool ; ø), _)
    (o!(υ _ true); ?(m); ε) <|> i?(m); !(m); ε).
  constructors.
Defined.

Example congruent_example1 : example1 ≡ example2. constructors. Qed.

Example example3 : PProcess.
  refine
  ([υ]> (new o <- (? Base bool ; ø), i <- (! Base bool ; ø), _)
    (o?(m); ε) <|> i!(υ _ true); ε).
  constructors.
Defined.

Example reduction_example1 : example2 ⇒ example3. constructors. Qed.

Example example4 : PProcess.
  refine
  ([υ]> (new i <- (! Base bool ; ø), o <- (? Base bool ; ø), _)
    (i!(υ _ true); ε <|> o?(m); ε)).
  constructors.
Defined.

Example congruent_example2 : example3 ≡ example4. constructors. Qed.

Example example5 : PProcess :=
  ([υ]> (new i <- ø, o <- ø, Ends) (ε i <|> ε o)).

Example reduction_example2 : example4 ⇒ example5. constructors. Qed.

Example big_step_reduction : example1 ⇒⇒ example5. big_step_reduction. Qed.

Example channel_over_channel : PProcess :=
  [υ]>
    (new i <- (? C[ ! Base bool ; ø ] ; ø), o <- (! C[ ! Base bool ; ø ] ; ø), (Leftwards Ends))
    (new i' <- (? Base bool ; ø), o' <- _, (Leftwards Ends))

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

Example congruent_example3: channel_over_channel ≡ channel_over_channel1. constructors. Qed.

Example nonlinear_example : PProcess :=
  [υ]> (new
    i <- (? Base bool ; ø),
    o <- (! Base bool; ø),
    (Leftwards Ends))

    (* Cheat the system by using the channel o twice *)
    i?(_); ε <|> o!(υ _ true); (fun _ => o!(υ _ true); ε)
    .

Example linear_example1 : Linear example1. compute. tauto. Qed.

Example nonlinear_example1 : ~ (Linear nonlinear_example).
Proof.
  compute; intros; decompose [and] H; discriminate.
Qed.
