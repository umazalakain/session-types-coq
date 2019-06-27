Require Import Unicode.Utf8.
Require Import Program.Equality.
Require Import Arith.
Require Import Forall.
Require Vectors.Vector.
Require Import Arith.Plus.
Import Vector.VectorNotations.

Inductive MType : Type :=
| Base : Set → MType
| Channel : SType → MType

with SType : Type :=
| ø : SType
| Send : MType → SType → SType
| Receive : MType → SType → SType
| Branch: ∀ {n}, Vector.t SType n → SType
| Select : ∀ {n}, Vector.t SType n → SType
.

Notation "C[ s ]" := (Channel s).
Notation "! m ; s" := (Send m s) (at level 90, right associativity).
Notation "? m ; s" := (Receive m s) (at level 90, right associativity).
Notation "▹ ss" := (Branch ss) (at level 90, right associativity).
Notation "◃ ss" := (Select ss) (at level 90, right associativity).

Inductive Duality : SType → SType → Prop :=
| Ends : Duality ø ø
| MRight : ∀ {m c₁ c₂}, Duality c₁ c₂ → Duality (Send m c₁) (Receive m c₂)
| MLeft : ∀ {m c₁ c₂}, Duality c₁ c₂ → Duality (Receive m c₁) (Send m c₂)
| SRight : ∀ {n} {xs ys : Vector.t SType n},
    Forall2 Duality xs ys → Duality (Select xs) (Branch ys)
| SLeft : ∀ {n} {xs ys : Vector.t SType n},
    Forall2 Duality xs ys → Duality (Branch xs) (Select ys)
.

Fixpoint inverse_duality {s r : SType} (d : Duality s r) : Duality r s :=
  (* Coq's termination checker complains if this is generalised *)
  let fix flipForall2 {n} {xs ys : Vector.t SType n}
          (ps : Forall2 Duality xs ys) : Forall2 Duality ys xs :=
      match ps with
      | Forall2_nil _ => Forall2_nil _
      | Forall2_cons _ _ _ _ _ p ps =>
        Forall2_cons _ _ _ _ _ (inverse_duality p) (flipForall2 ps)
      end
  in match d with
  | Ends => Ends
  | MRight d' => MLeft (inverse_duality d')
  | MLeft d' => MRight (inverse_duality d')
  | SRight d' => SLeft (flipForall2 d')
  | SLeft d' => SRight (flipForall2 d')
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

  | PBranch
    : ∀ {n : nat} {ss : Vector.t SType n}
    , Forall (fun s => Message C[s] → Process) ss
    → Message C[Branch ss]
    → Process

  | PSelect
    : ∀ {n : nat} {ss : Vector.t SType n}
    (i : Fin.t n)
    , (Message C[ss[@i]] → Process)
    → Message C[Select ss]
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

  | CReflexive P :
      P ≡ P

  | CTransitive P Q R :
      P ≡ Q → Q ≡ R → P ≡ R

  where "P ≡ Q" := (Congruence P Q)
  .

  Reserved Notation "P ⇒ Q" (at level 60).
  Inductive Reduction : Process -> Process -> Prop :=
  | RComm mt s r sDr P Q : forall (m : Message mt),
      PNew (! mt; s) (? mt; r) (MRight sDr)
           (fun a b => PComp (POutput m Q a) (PInput P b)) ⇒
      PNew s r sDr
           (fun a b => PComp (Q a) (P m b))

  | RCase n mt {ss rs : Vector.t SType n} sDr {i : Fin.t n} Ps Qs : forall (m : Message mt),
      PNew (Select ss) (Branch rs) (SRight sDr)
           (fun a b => PComp (PSelect i Ps a) (PBranch Qs b)) ⇒
      PNew ss[@i] rs[@i] (nthForall2 sDr i)
           (fun a b => PComp (Ps a) (nthForall Qs i b))

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
Notation "◃( i ); p" := (PSelect _ _ i p)(at level 80).
Notation "c ◃( i ); p" := (PSelect _ _ i p c)(at level 79).
Notation "▹( ps )" := (PBranch _ _ ps)(at level 80).
Notation "c ▹ ps" := (PBranch _ _ ps c)(at level 79).
Definition ε {ST : Type} {MT: Type → Type} : Message ST MT (Channel ø) → Process ST MT:= PEnd ST MT.

Arguments V [ST MT M].
Arguments C [ST MT S].
Arguments PNew [ST MT].
Arguments PInput [ST MT m s].
Arguments POutput [ST MT m s].
Arguments PSelect [ST MT n ss].
Arguments PBranch [ST MT n ss].
Arguments PComp [ST MT].
Arguments PEnd [ST MT].

(**************************)
(*       LINEARITY        *)
(**************************)

Definition TMT : Type → Type := fun _ => unit.
Definition fMT : ∀ (S: Set), S → Message bool TMT (Base S) := fun _ _ => V tt.

Definition is_marked {MT : Type → Type} {mt : MType} (m : Message bool MT mt) : bool :=
  match m with
  | V _ => false
  | C m => m
  end
.
Notation "'count_if_marked' c" := (if is_marked c then 1 else 0)(at level 50).
Definition marked : ∀ s, Message bool TMT C[s] := fun s => C true.
Definition unmarked : ∀ s, Message bool TMT C[s] := fun s => C false.
Arguments marked [s].
Arguments unmarked [s].
Hint Unfold is_marked.
Hint Unfold marked.
Hint Unfold unmarked.

(* Always recurse by passing unmarked arguments.
   If the constructor accepts a channel as an argument, it has been used.
   If a channel is sent as output, it has been used.
   Channels received as input are considered fresh.
*)

Definition branch_input {ST MT A B mt}
           (P : Message ST MT mt → A)
           (MP : ∀ {bmt}, (Message ST MT (Base bmt) → A) → B)
           (CP : ∀ {smt}, (Message ST MT (Channel smt) → A) → B) : B :=
  (match mt as mt' return (Message ST MT mt' → A) → B with
   | Base _ => fun P' => MP P'
   | Channel _ => fun P' => CP P'
   end) P
.
Hint Unfold branch_input.

Fixpoint count_marked (p : Process bool TMT) : nat :=
  let fix count_branches {n} {ss : Vector.t SType n}
          (ps : Forall (fun s => Message _ _ C[s] → Process _ _) ss) : nat :=
       match ps with
       | Forall_nil _ => 0
       | Forall_cons _ _ _ p ps' => count_marked (p unmarked) + count_branches ps'
       end
  in
  match p with
  | PNew _ _ _ p => count_marked (p unmarked unmarked)

  | PInput p c =>
    count_if_marked c + branch_input p
      (fun _ p' => count_marked (p' (V tt) unmarked))
      (fun _ p' => count_marked (p' unmarked unmarked))

  | POutput m p c =>
    count_if_marked c + count_if_marked m + count_marked (p unmarked)

  | PBranch p c =>
    count_if_marked c + count_branches p

  | PSelect i p c =>
    count_if_marked c + count_marked (p unmarked)

  | PComp l r  => count_marked l + count_marked r

  | PEnd c => count_if_marked c
  end
.

Notation "'none_marked' p" := (count_marked p = 0)(at level 50).
Notation "'single_marked' p" := (count_marked p = 1)(at level 50).

Fixpoint linear (p : Process bool TMT) : Prop :=
  let fix linear_branches {n} {ss : Vector.t SType n}
          (ps : Forall (fun s => Message _ _ C[s] → Process _ _) ss) : Prop :=
       match ps with
       | Forall_nil _ => True
       | Forall_cons _ _ _ p ps' =>
         single_marked (p marked) /\
         linear (p unmarked) /\
         linear_branches ps'
       end
  in
  none_marked p /\ (
    match p with
    | PNew _ _ _ p =>
      single_marked (p marked unmarked) /\
      single_marked (p unmarked marked) /\
      linear (p unmarked unmarked)

    | PInput p _ => branch_input p
       (fun _ p' => single_marked (p' (V tt) marked) /\
                 linear (p' (V tt) unmarked))
       (fun _ p' => single_marked (p' marked unmarked) /\
                 single_marked (p' unmarked marked) /\
                 linear (p' unmarked unmarked))

    | POutput _ p _ => single_marked (p marked) /\ linear (p unmarked)

    | PBranch p _ => linear_branches p

    | PSelect _ p _ => single_marked (p marked) /\ linear (p unmarked)

    | PComp l r => linear l /\ linear r

    | PEnd _ => True
    end
  )
.

(******************************)
(*  PARAMETRIC GENERALISATION *)
(******************************)

(* Abstract over parametric types and their constructors *)
Definition PProcess := ∀ ST MT (mf : ∀ (S: Set), S → Message ST MT (Base S)) , Process ST MT.
Definition Linear (p : PProcess) : Prop := linear (p bool TMT fMT).
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
  repeat (
  try match goal with
  | [ H : linear _ |- _ ] => destruct H
  end;
  try match goal with
  | [ H : and _ _ |- _ ] => destruct H
  end;
  autounfold with * in *
  )
.


(******************************************)
(*          TYPE PRESERVATION             *)
(******************************************)

Lemma false_unmarked s : @C bool _ s false = unmarked. eauto. Qed.
Hint Rewrite false_unmarked.

Lemma linearity_count {P} : linear P → count_marked P = 0.
Proof.
  intro lP.
  induction P.
  all: simpl; destruct_linear; eauto.
Qed.
Hint Resolve linearity_count.

Lemma congruence_count {P Q} : Congruence _ _ P Q → count_marked P = count_marked Q.
Proof.
  intros PcQ.
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
  all: simpl; destruct_linear.
  + rewrite (linearity_count H0).
    rewrite (linearity_count H1).
    auto.
  + rewrite (linearity_count H1).
    rewrite (linearity_count H2).
    rewrite (linearity_count H3).
    eauto.
  + rewrite (linearity_count (IHPcQ1 H0)).
    rewrite (linearity_count (IHPcQ2 H1)).
    eauto.
  + rewrite (linearity_count (H0 _ _ H6)).
    rewrite (linearity_count H3).
    repeat rewrite <- (congruence_count (H _ _)).
    rewrite H4.
    rewrite H5.
    repeat split; eauto.
  + rewrite <- (congruence_count (H _ _ _ _)).
    rewrite <- (congruence_count (H (C true) _ _ _)).
    rewrite <- (congruence_count (H _ (C true) _ _)).
    rewrite <- (congruence_count (H _ _ (C true) _)).
    rewrite <- (congruence_count (H _ _ _ (C true))).
    repeat split; eauto.
  + rewrite <- (congruence_count (H _ _)).
    rewrite <- (congruence_count (H (C true) _)).
    rewrite <- (congruence_count (H _ (C true))).
    repeat split; eauto.
  + rewrite <- (congruence_count (H _ _)).
    rewrite <- (congruence_count (H (C true) _)).
    rewrite <- (congruence_count (H _ (C true))).
    repeat split; eauto.
  + simpl in *.
    destruct (plus_is_O _ _ H1).
    destruct (plus_is_O _ _ H5).
    rewrite <- (congruence_count (H _)).
    rewrite <- (congruence_count (H (C true))).
    repeat split; eauto.
  + dependent induction mt.
    destruct_linear.
    rewrite <- (congruence_count (H _ _)).
    rewrite <- (congruence_count (H _ (C true))).
    eauto.
    destruct_linear.
    rewrite <- (congruence_count (H _ _)).
    rewrite <- (congruence_count (H _ (C true))).
    rewrite <- (congruence_count (H (C true) _)).
    repeat split; eauto.
  + assumption.
  + eauto.
Qed.

Theorem linearity_preservation : ∀ P Q, Reduction _ _ P Q → linear P → linear Q.
  intros P Q PrQ lP.
  dependent induction PrQ.
  - simpl.
    dependent induction m.
    + destruct_linear.
      simpl in *.
      repeat rewrite false_unmarked in *.
      destruct m.
      rewrite H, H3, H4, H5, H6.
      repeat split; eauto.
    + destruct_linear.
      induction s0.
      discriminate H3.
      repeat rewrite false_unmarked in *.
      simpl in *.
      rewrite H3, H4, H6, H7.
      repeat split; eauto.
  - admit.
  - exact (linearity_under_bindings H0 lP).
  - destruct_linear.
    simpl in *.
    destruct (plus_is_O _ _ H).
    rewrite H3.
    rewrite (linearity_count (IHPrQ H0)).
    repeat split; eauto.
  - exact (IHPrQ (linearity_congruence _ _ H lP)).
Admitted.

Theorem TypePreservation : ∀ (P Q : PProcess), P ⇒ Q → Linear P → Linear Q.
Proof.
  intros P Q PrQ lP.
  unfold PProcess in P, Q.
  unfold Linear.
  unfold Linear in lP.
  refine (
      (match (P bool TMT fMT) as P'
             return linear P' → Reduction _ _ P' (Q bool TMT fMT) → linear (Q bool TMT fMT)
       with
       | _ => _
       end) lP (PrQ bool TMT fMT)).
  all: intros slP sPrQ.
  exact (linearity_preservation (P _ _ _) (Q _ _ _) sPrQ slP).
Qed.

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
    (new i <- (? C[ ! Base bool ; ø ] ; ø), o <- (! C[ ! Base bool ; ø ] ; ø), (MLeft Ends))
    (new i' <- (? Base bool ; ø), o' <- _, (MLeft Ends))

    (i?(c); fun a => ε a <|> c!(υ _ true); ε)
    <|>
    (o!(o'); fun a => ε a <|> i'?(_); ε)
.

Example channel_over_channel1 : PProcess :=
  [υ]>
    (new i' <- (? Base bool ; ø), o' <- (! Base bool ; ø), (MLeft Ends))
    (new i <- (? C[ ! Base bool ; ø ] ; ø), o <- (! C[ ! Base bool ; ø ] ; ø), (MLeft Ends))

    (i?(c); fun a => c!(υ _ true); ε <|> ε a)
    <|>
    (o!(o'); fun a => i'?(_); ε <|> ε a)
.

Example congruent_example3: channel_over_channel ≡ channel_over_channel1. constructors. Qed.

Example nonlinear_example : PProcess :=
  [υ]> (new
    i <- (? Base bool ; ø),
    o <- (! Base bool; ø),
    (MLeft Ends))

    (* Cheat the system by using the channel o twice *)
    i?(_); ε <|> o!(υ _ true); (fun _ => o!(υ _ true); ε)
    .

Example linear_example1 : Linear example1. compute. tauto. Qed.

Example nonlinear_example1 : ~ (Linear nonlinear_example).
Proof.
  compute; intros; decompose [and] H; discriminate.
Qed.
