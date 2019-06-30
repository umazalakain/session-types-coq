Require Import Unicode.Utf8.
Require Import Program.Equality.
Require Import Arith.
Require Import Forall.
Require Vectors.Vector.
Require Import Arith.Plus.
Import Vector.VectorNotations.
From Equations Require Import Equations.

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
    , Message C[Select ss]
    → (Message C[ss[@i]] → Process)
    → Process

  | PComp : Process → Process → Process

  | PEnd : Message C[ø] → Process
  .

  Reserved Notation "P ≡ Q" (no associativity, at level 80).
  Inductive Congruence : Process → Process → Prop :=
  | CCompCommutative {P Q} :
      PComp P Q ≡ PComp Q P

  | CCompAssociative {P Q R} :
      PComp (PComp P Q) R ≡ PComp P (PComp Q R)

  | CCompCongruent {P Q R S} :
      P ≡ Q → R ≡ S → PComp P R ≡ PComp Q S

  | CScopeExpansion {s r sDr P Q R} :
      (∀ (a : Message C[s]) (b : Message C[r]), P a b ≡ Q a b) →
      PComp (PNew s r sDr P) R ≡ PNew s r sDr (fun a b => PComp (Q a b) R)

  | CScopeCommutative {s r sDr s' r' sDr' P Q} :
      (∀ (a : Message C[s]) (b : Message C[r]) (c : Message C[s']) (d : Message C[r']), P a b c d ≡ Q a b c d) →
      PNew s r sDr (fun a b => PNew s' r' sDr' (fun c d => P a b c d)) ≡
      PNew s' r' sDr' (fun c d => PNew s r sDr (fun a b => Q a b c d))

  | CNewTypesCommutative {s r sDr P Q} :
      (∀ (a : Message C[s]) (b : Message C[r]), P a b ≡ Q a b) →
      PNew s r sDr (fun a b => P a b) ≡ PNew r s (inverse_duality sDr) (fun b a => Q a b)

  | CNewCongruent {s r sDr P Q} :
      (∀ (a : Message C[s]) (b : Message C[r]), P a b ≡  Q a b) →
      PNew s r sDr P ≡ PNew s r sDr Q

  | COutputCongruent {mt st} {m : Message mt} {c : Message C[! mt; st]} {P Q} :
      (∀ (a : Message C[st]), P a ≡ Q a) →
      POutput m P c ≡ POutput m Q c

  | CInputCongruent {mt st} {c : Message C[? mt; st]} {P Q} :
      (∀ (a : Message mt) (b : Message C[st]), P a b ≡ Q a b) →
      PInput P c ≡ PInput Q c

  | CReflexive P :
      P ≡ P

  | CTransitive {P} Q {R} :
      P ≡ Q → Q ≡ R → P ≡ R

  where "P ≡ Q" := (Congruence P Q)
  .

  Reserved Notation "P ⇒ Q" (at level 60).
  Inductive Reduction : Process -> Process -> Prop :=
  | RComm {mt s r sDr P Q} {m : Message mt} :
      PNew (! mt; s) (? mt; r) (MRight sDr)
           (fun a b => PComp (POutput m Q a) (PInput P b)) ⇒
      PNew s r sDr
           (fun a b => PComp (Q a) (P m b))

  | RCase {n mt} {i : Fin.t n} {ss rs : Vector.t SType n} {sDr} {Ps Qs} {m : Message mt} :
      PNew (Select ss) (Branch rs) (SRight sDr)
           (fun a b => PComp (PSelect i a Ps) (PBranch Qs b)) ⇒
      PNew ss[@i] rs[@i] (nthForall2 sDr i)
           (fun a b => PComp (Ps a) (nthForall Qs i b))

  | RRes {s r P Q} :
      (∀ (a : Message C[s]) (b : Message C[r]), P a b ⇒ Q a b) →
      (∀ (sDr : Duality s r), PNew s r sDr P ⇒ PNew s r sDr Q)

  | RPar {P Q R} :
      P ⇒ Q → PComp P R ⇒ PComp Q R

  | RStruct {P Q R} :
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
Notation "![ m ]; p" := (POutput _ _ m p)(at level 80).
Notation "c ![ m ]; p" := (POutput _ _ m p c)(at level 79).
Notation "?[ m ]; p" := (PInput _ _ (fun m => p))(at level 80).
Notation "c ?[ m ]; p" := (PInput _ _ (fun m => p) c)(at level 79).
Notation "◃[ i ]; p" := (fun c => PSelect _ _ i c p)(at level 80).
Notation "c ◃[ i ]; p" := (PSelect _ _ i c p)(at level 79).
Notation "▹[ x ; .. ; y ]" :=
  (PBranch _ _ (Forall_cons _ x .. (Forall_cons _ y (Forall_nil _)) ..))(at level 80).
Notation "c ▹[ x ; .. ; y ]" :=
  (PBranch _ _ (Forall_cons _ x .. (Forall_cons _ y (Forall_nil _)) ..) c)(at level 79).
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

Definition marked : ∀ s, Message bool TMT C[s] := fun s => C true.
Definition unmarked : ∀ s, Message bool TMT C[s] := fun s => C false.
Arguments marked [s].
Arguments unmarked [s].

(* Always recurse by passing unmarked arguments.
   If the constructor accepts a channel as an argument, it has been used.
   If a channel is sent as output, it has been used.
   Channels received as input are considered fresh.
*)

Derive NoConfusion for MType.
Derive Signature for Message.

(* t means "Has it been already found?" *)
Equations find (t : bool) (p : Process bool TMT) : Prop :=
find _     (PNew _ _ _ P)                  => find t (P (C false) (C false)) ;
find true  (PInput P (C true))             => False ;
find t     (@PInput (Base _) _ P (C c))    => find (t || c) (P (V tt) (C false)) ;
find t     (@PInput (Channel _) _ P (C c)) => if (orb t c)
                                             then and (find true (P (C false) (C false)))
                                                      (find false (P (C true) (C false)))
                                             else find false (P (C false) (C false)) ;
find true  (POutput m P (C true))          => False ;
find t     (POutput (V _) P (C c))         => find (t || c) (P (C false)) ;
find true  (POutput (C true) P (C false))  => False ;
find _     (POutput (C true) P (C true))   => False ;
find t     (POutput (C c) P (C false))     => find (t || c) (P (C false)) ;
find t     (POutput (C false) P (C c))     => find (t || c) (P (C false)) ;
find true  (PComp P Q)                     => and (find true P) (find true Q) ;
find false (PComp P Q)                     => or (and (find true P) (find false Q))
                                                (and (find false P) (find true Q)) ;
find true  (PEnd (C true))                 => False ;
find false (PEnd (C false))                => False ;
find _     (PEnd (C _))                    => True ;
find true  (PSelect i (C true) P)          => False ;
find t     (PSelect i (C c) P)             => find (t || c) (P (C false)) ;
find true  (PBranch Ps (C true))           => False ;
find t     (PBranch Ps (C c))              =>
  (* Coq's termination checker complains if this is generalised *)
  let fix find_branches {n} {ss : Vector.t SType n}
          (ps : Forall (fun s => Message _ _ C[s] → Process _ _) ss) : Prop :=
       match ps with
       | Forall_nil _ => True
       | Forall_cons _ P Ps' => find (t || c) (P (C false)) /\ find_branches Ps'
       end
  in
  find_branches Ps
.
Global Transparent find.

Notation "'none_marked' p" := (find true p)(at level 50).
Notation "'single_marked' p" := (find false p)(at level 50).

Equations linear (P : Process bool TMT) : Prop := {
linear P => none_marked P /\ linear_do P }
where
linear_do (P : Process bool TMT) : Prop :=
linear_do (PNew _ _ _ P) =>
  single_marked (P marked unmarked) /\
  single_marked (P unmarked marked) /\
  linear (P unmarked unmarked) ;

linear_do (@PInput (Base _) _ P _) =>
  single_marked (P (V tt) marked) /\
  linear (P (V tt) unmarked) ;

linear_do (@PInput (Channel _) _ P _) =>
  single_marked (P marked unmarked) /\
  single_marked (P unmarked marked) /\
  linear (P unmarked unmarked) ;

linear_do (POutput _ P _) =>
  single_marked (P marked) /\
  linear (P unmarked) ;

linear_do (PComp P Q) =>
  linear P /\
  linear Q ;

linear_do (PEnd _) => True ;

linear_do (PSelect _ _ P) =>
  single_marked (P marked) /\
  linear (P unmarked) ;

linear_do (PBranch Ps _) =>
  (* Coq's termination checker complains if this is generalised *)
  let fix linear_branches {n} {ss : Vector.t SType n}
          (ps : Forall (fun s => Message _ _ C[s] → Process _ _) ss) : Prop :=
       match ps with
       | Forall_nil _ => True
       | Forall_cons _ P Ps' =>
         single_marked (P marked) /\
         linear (P unmarked) /\
         linear_branches Ps'
       end
  in
  linear_branches Ps
.
Global Transparent linear.

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
  | [ |- Reduction _ _ (PNew _ _ ?D (fun a b => b?[m]; ?PB <|> a![?M]; ?PA)) _ ] =>
    apply RStruct with (PNew _ _ D (fun a b => a![M]; PA <|> b?[m]; PB))
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
  | [ H : find _ _ |- _ ] => destruct H
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

Lemma linearity_none_marked {P} : linear P → none_marked P.
Proof.
  intro lP.
  induction P.
  all: simpl; destruct_linear; eauto.
Qed.
Hint Resolve linearity_none_marked.

Lemma congruence_find {P Q} : Congruence _ _ P Q → ∀ t, find t P → find t Q.
  intros PcQ t fP.
  dependent induction PcQ; induction t; simpl; intuition; try tauto.
  - destruct_linear; auto.
  - destruct_linear; auto.
  - destruct_linear.
    left.
    auto.
    right.
    auto.
  - destruct_linear.
    left.
    auto.
    right.
    auto.
  - dependent induction c.
    dependent induction m.
    destruct m.
    destruct s.
    contradiction.
    exact (H0 _ true fP).
    destruct s.
    contradiction.
    destruct s0.
    contradiction.
    exact (H0 _ true fP).
  - dependent induction c.
    dependent induction m.
    destruct m.
    destruct s.
    exact (H0 _ true fP).
    exact (H0 _ false fP).
    destruct s0.
    destruct s.
    contradiction fP.
    exact (H0 _ true fP).
    destruct s.
    exact (H0 _ true fP).
    exact (H0 _ false fP).
  - dependent induction c.
    dependent induction mt.
    destruct s.
    contradiction.
    exact (H0 _ _ true fP).
    destruct s0.
    contradiction.
    destruct fP.
    split.
    exact (H0 _ _ true H1).
    exact (H0 _ _ false H2).
  - dependent induction c.
    dependent induction mt.
    destruct s.
    exact (H0 _ _ true fP).
    exact (H0 _ _ false fP).
    destruct s0.
    destruct fP.
    split.
    exact (H0 _ _ true H1).
    exact (H0 _ _ false H2).
    exact (H0 _ _ false fP).
Qed.
Hint Resolve congruence_find.

Theorem congruence_linearity {P Q} : Congruence _ _ P Q → linear P → linear Q.
Proof.
  intros PcQ lP.
  induction PcQ; simpl; destruct_linear; auto.
  - pose (congruence_find (H _ _) true H1).
    pose (congruence_find (H _ _) false H5).
    pose (congruence_find (H _ _) false H6).
    repeat split; auto.
  - pose (congruence_find (H _ _ _ _) true H1).
    pose (congruence_find (H _ _ _ _) false H2).
    pose (congruence_find (H _ _ _ _) false H3).
    pose (congruence_find (H _ _ _ _) false H5).
    pose (congruence_find (H _ _ _ _) false H6).
    repeat split; auto.
  - pose (congruence_find (H _ _) true H1).
    pose (congruence_find (H _ _) false H2).
    pose (congruence_find (H _ _) false H3).
    repeat split; auto.
  - pose (congruence_find (H _ _) true H1).
    pose (congruence_find (H _ _) false H2).
    pose (congruence_find (H _ _) false H3).
    repeat split; auto.
  - dependent induction c.
    dependent induction s.
    contradiction H1.
    dependent induction m.
    pose (congruence_find (H _) true H1).
    pose (congruence_find (H _) false H2).
    auto.
    dependent induction s.
    contradiction H1.
    pose (congruence_find (H _) true H1).
    pose (congruence_find (H _) false H2).
    auto.
  - dependent induction mt.
    dependent induction c.
    dependent induction s.
    contradiction H1.
    decompose [and] H2.
    pose (congruence_find (H _ _) true H1).
    pose (congruence_find (H _ _) false H3).
    auto.
    dependent induction c.
    dependent induction s0.
    contradiction H1.
    decompose [and] H2.
    destruct H1.
    repeat split; eauto.
Qed.

Lemma reduction_find {P Q} : Reduction _ _ P Q → ∀ t, find t P → find t Q.
  intros PrQ t fP.
  dependent induction PrQ; induction t; simpl; intuition; try tauto.
  - destruct_linear.
    destruct m.
    destruct t.
    assumption.
    destruct b.
    contradiction.
    assumption.
  - destruct_linear.
    destruct m.
    destruct t.
    assumption.
    destruct b.
    destruct H0.
    contradiction.
    destruct H0.
    assumption.
  - destruct_linear.
    destruct m.
    destruct t.
    auto.
    destruct b.
    contradiction.
    left.
    auto.
    destruct m.
    destruct t.
    auto.
    destruct b.
    destruct H0.
    left.
    auto.
    destruct H0.
    right.
    auto.
  - admit.
  - admit.
  - destruct_linear.
    left.
    auto.
    right.
    auto.
  - exact (IHPrQ true (congruence_find H true fP)).
  - exact (IHPrQ false (congruence_find H false fP)).
Admitted.

Theorem reduction_linearity {P Q} : Reduction _ _ P Q → linear P → linear Q.
  intros PrQ lP.
  dependent induction PrQ.
  - simpl.
    dependent induction m.
    + destruct_linear.
      simpl in *.
      destruct m.
      repeat split; eauto.
    + destruct_linear.
      induction s0.
      contradiction.
      repeat split; eauto.
  - dependent induction i; dependent destruction Qs.
    + simpl in *.
      decompose [and] lP.
      repeat split; eauto.
    + dependent destruction ss.
      simpl in Ps.
      simpl in lP.
      decompose [and] lP.
      refine (IHi _ _ _ Ps Qs _ _).
      dependent destruction mt.
      exact (V tt).
      exact (C false).
      simpl in *.
      admit.
      (*
      pose (linearity_none_marked H8).
      repeat split; eauto.
*)
  - destruct_linear.
    pose (reduction_find (H _ _) true H1).
    pose (reduction_find (H _ _) false H2).
    pose (reduction_find (H _ _) false H3).
    repeat split; auto.
  - destruct_linear.
    repeat split; eauto.
  - exact (IHPrQ (congruence_linearity H lP)).
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
  exact (reduction_linearity sPrQ slP).
Qed.

(******************************************)
(*               EXAMPLES                 *)
(******************************************)

Example example1 : PProcess.
  refine
  ([υ]> (new i <- _, o <- _, _)
    (i?[m]; ![m]; ε) <|> (o![υ _ true]; ?[m]; ε)).
  constructors.
Defined.
Print example1.

Example example2 : PProcess.
  refine
  ([υ]> (new o <- ! Base bool ; ? Base bool ; ø, i <- ? Base bool ; ! Base bool ; ø, _)
    (o![υ _ true]; ?[m]; ε) <|> i?[m]; ![m]; ε).
  constructors.
Defined.

Example congruent_example1 : example1 ≡ example2. constructors. Qed.

Example example3 : PProcess.
  refine
  ([υ]> (new o <- ? Base bool ; ø, i <- ! Base bool ; ø, _)
    (o?[m]; ε) <|> i![υ _ true]; ε).
  constructors.
Defined.

Example reduction_example1 : example2 ⇒ example3. constructors. Qed.

Example example4 : PProcess.
  refine
  ([υ]> (new i <- ! Base bool ; ø, o <- ? Base bool ; ø, _)
    (i![υ _ true]; ε <|> o?[m]; ε)).
  constructors.
Defined.

Example congruent_example2 : example3 ≡ example4. constructors. Qed.

Example example5 : PProcess :=
  ([υ]> (new i <- ø, o <- ø, Ends) (ε i <|> ε o)).

Example reduction_example2 : example4 ⇒ example5. constructors. Qed.

Example big_step_reduction : example1 ⇒⇒ example5. big_step_reduction. Qed.

Example channel_over_channel : PProcess :=
  [υ]>
    (new i <- ? C[ ! Base bool ; ø ] ; ø, o <- ! C[ ! Base bool ; ø ] ; ø, MLeft Ends)
    (new i' <- ? Base bool ; ø, o' <- _, MLeft Ends)

    (i?[c]; fun a => ε a <|> c![υ _ true]; ε)
    <|>
    (o![o']; fun a => ε a <|> i'?[_]; ε)
.

Example channel_over_channel1 : PProcess :=
  [υ]>
    (new i' <- ? Base bool ; ø, o' <- ! Base bool ; ø, MLeft Ends)
    (new i <- ? C[ ! Base bool ; ø ] ; ø, o <- ! C[ ! Base bool ; ø ] ; ø, MLeft Ends)

    (i?[c]; fun a => c![υ _ true]; ε <|> ε a)
    <|>
    (o![o']; fun a => i'?[_]; ε <|> ε a)
.

Example congruent_example3: channel_over_channel ≡ channel_over_channel1. constructors. Qed.

Example nonlinear_example : PProcess :=
  [υ]> (new i <- ? Base bool ; ø, o <- ! Base bool; ø, MLeft Ends)

    (* Cheat the system by using the channel o twice *)
    i?[_]; ε <|> o![υ _ true]; (fun _ => o![υ _ true]; ε)
    .

Example linear_example1 : Linear example1. compute. tauto. Qed.

Example nonlinear_example1 : ~ (Linear nonlinear_example). compute. tauto. Qed.

Example branch_and_select : PProcess.
refine
  ([υ]> (new i <- ▹ (! Base bool; ø) :: (? Base bool; ø) :: [], o <- ◃ (? Base bool; ø) :: (! Base bool; ø) :: [], _)
          i▹[ (![υ _ true]; ε) ; (?[m]; ε)] <|> o◃[Fin.F1]; ?[_]; ε).
