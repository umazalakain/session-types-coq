Require Import Unicode.Utf8.
Require Import Program.Equality.
Require Import Forall.
Require Vectors.Vector.
Import Vector.VectorNotations.
From Equations Require Import Equations.

Inductive MType : Type :=
| Base : Type → MType
| Channel : SType → MType

with SType : Type :=
| ø : SType
| Send : MType → SType → SType
| Receive : MType → SType → SType
| Branch: ∀ {n}, Vector.t SType n → SType
| Select : ∀ {n}, Vector.t SType n → SType
.

Notation "B[ s ]" := (Base s).
Notation "C[ s ]" := (Channel s).
Notation "! m ; s" := (Send m s) (at level 90, right associativity).
Notation "? m ; s" := (Receive m s) (at level 90, right associativity).
Notation "&{ ss }" := (Branch ss) (at level 90, right associativity).
Notation "⊕{ ss }" := (Select ss) (at level 90, right associativity).

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
  | V : ∀ {M : Type}, MT M → Message B[M]
  | C : ∀ {S : SType}, ST → Message C[S]
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

  Reserved Notation "P ⇒* Q" (at level 60).
  Inductive RTReduction : Process → Process → Prop :=
  | RRefl P : P ⇒* P
  | RStep P Q R : P ⇒ Q → Q ⇒* R → P ⇒* R
  where "P ⇒* Q" := (RTReduction P Q)
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
Notation "◃ i ; p" := (fun c => PSelect _ _ i c p)(at level 80).
Notation "c ◃ i ; p" := (PSelect _ _ i c p)(at level 79).
Notation "▹{ x ; .. ; y }" :=
  (PBranch _ _ (Forall_cons _ x .. (Forall_cons _ y (Forall_nil _)) ..))(at level 80).
Notation "c ▹{ x ; .. ; y }" :=
  (PBranch _ _ (Forall_cons _ x .. (Forall_cons _ y (Forall_nil _)) ..) c)(at level 79).
Definition ε {ST : Type} {MT: Type → Type} : Message ST MT C[ø] → Process ST MT:= PEnd ST MT.

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
Definition fMT : ∀ (S: Set), S → Message bool TMT B[S] := fun _ _ => V tt.

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

Equations linear (P : Process bool TMT) : Prop := {
linear (PNew _ _ _ P) =>
  single_marked (P marked unmarked) /\
  single_marked (P unmarked marked) /\
  linear (P unmarked unmarked) ;
linear (@PInput m _ P c) with c => {
| (C true) => False ;
| (C false) with m => {
  | B[_] =>
    single_marked (P (V tt) marked) /\
    linear (P (V tt) unmarked) ;
  | C[_] =>
    single_marked (P marked unmarked) /\
    single_marked (P unmarked marked) /\
    linear (P unmarked unmarked)}};
linear (POutput m P c) with c => {
| (C true) => False ;
| (C false) with m => {
  | (C true) => False ;
  | _ =>
    single_marked (P marked) /\
    linear (P unmarked)}};
linear (PComp P Q) => linear P /\ linear Q ;
linear (PEnd c) with c => {
| (C true) => False ;
| (C false) => True};
linear (PSelect _ c P) with c => {
| (C true) => False ;
| (C false) =>
  single_marked (P marked) /\
  linear (P unmarked)};
linear (PBranch Ps c) with c => {
| (C true) => False ;
| (C false) =>
  let fix branches {n} {ss : Vector.t _ n} (Ps : Forall (fun s => _ → _) ss) :=
      match Ps with
      | Forall_nil _ => True
      | Forall_cons _ P Ps' =>
        linear (P unmarked) /\
        single_marked (P marked) /\
        branches Ps'
      end
  in branches Ps}

} where single_marked (p : Process bool TMT) : Prop := {

single_marked (PNew _ _ _ P) => single_marked (P unmarked unmarked) ;
single_marked (@PInput m _ P c) with c => {
| (C true) with m => {
  | B[_] =>
    linear (P (V tt) unmarked) /\
    single_marked (P (V tt) marked);
  | C[_] =>
    linear (P unmarked unmarked) /\
    single_marked (P marked unmarked) /\
    single_marked (P unmarked marked)};
| (C false) with m => {
  | B[_] => single_marked (P (V tt) unmarked) ;
  | C[_] => single_marked (P unmarked unmarked)}};
single_marked (POutput m P c) with c => {
| (C true) with m => {
  | (C true) => False ;
  | _ => linear (P unmarked) /\ single_marked (P marked)};
| (C false) with m => {
  | (C true) => linear (P unmarked) /\ single_marked (P marked) ;
  | _ => single_marked (P unmarked)}};
single_marked (PComp P Q) =>
  (linear P /\ single_marked Q) \/
  (single_marked P /\ linear Q) ;
single_marked (PEnd c) with c => {
| (C true) => True;
| (C false) => False};
single_marked (PSelect i c P) with c => {
| (C true) => linear (P unmarked) /\ single_marked (P marked) ;
| (C false) => single_marked (P unmarked)};
single_marked (PBranch Ps c) with c => {
| (C true) =>
  let fix branches {n} {ss : Vector.t _ n} (Ps : Forall (fun s => _ → _) ss) :=
      match Ps with
      | Forall_nil _ => True
      | Forall_cons _ P Ps' =>
        linear (P unmarked) /\
        single_marked (P marked) /\
        branches Ps'
      end
  in branches Ps ;
| (C false) =>
  let fix branches {n} {ss : Vector.t _ n} (Ps : Forall (fun s => _ → _) ss) :=
      match Ps with
      | Forall_nil _ => True
      | Forall_cons _ P Ps' =>
        single_marked (P unmarked) /\
        branches Ps'
      end
  in branches Ps
}}.

(******************************)
(*  PARAMETRIC GENERALISATION *)
(******************************)

(* Abstract over parametric types and their constructors *)
Definition PProcess := ∀ ST MT (mf : ∀ (S: Set), S → Message ST MT B[S]) , Process ST MT.
Definition Linear (p : PProcess) : Prop := linear (p bool TMT fMT).
Notation "[ f ]> P" := (fun _ _ f => P)(at level 80).
Notation "P ≡ Q" := (∀ ST MT mf, Congruence _ _ (P ST MT mf) (Q ST MT mf))(at level 80).
Notation "P ⇒ Q" := (∀ ST MT mf, Reduction _ _ (P ST MT mf) (Q ST MT mf))(at level 80).
Notation "P ⇒* Q" := (∀ ST MT mf, RTReduction _ _ (P ST MT mf) (Q ST MT mf))(at level 80).

(*****************************)
(*         PROGRESS          *)
(*****************************)

Fixpoint completed (P : Process unit id) : Prop :=
  match P with
  | (PNew ø ø _ P) => completed (P (C tt) (C tt))
  | (PComp P Q) => completed P /\ completed Q
  | (PEnd _) => True
  | _ => False
  end
.
Definition Completed (P : PProcess) : Prop := completed (P unit id (fun _ v => V v)).

Definition Completes (P : PProcess) := exists Q, P ⇒⇒ Q /\ Completed Q.

(*********************************)
(*      REDUCTION TACTICS        *)
(*********************************)

Ltac constructors :=
  repeat (intros; compute; constructor)
.
Hint Extern 1 (Duality _ _) => constructors.
Hint Extern 1 (_ ≡ _) => constructors.

Ltac linearity_hypotheses :=
  match goal with
  | [ s : SType, r : SType , s' : SType, r' : SType |- _ ] =>
    match goal with
    | [ H : Message bool TMT C[s] → Message bool TMT C[r] →
            Message bool TMT C[s'] → Message bool TMT C[r'] →
            _ |- _ ] =>
      destruct (H unmarked unmarked unmarked unmarked);
      destruct (H marked unmarked unmarked unmarked);
      destruct (H unmarked marked unmarked unmarked);
      destruct (H unmarked unmarked marked unmarked);
      destruct (H unmarked unmarked unmarked marked)
    end
  | [ s : SType, r : SType |- _ ] =>
    match goal with
    | [ H : ∀ (a : Message bool TMT C[s]) (b : Message bool TMT C[r]), _ |- _ ] =>
      destruct (H unmarked unmarked);
      destruct (H unmarked marked);
      destruct (H marked unmarked)
    end
  | [ T : Type, s : SType |- _ ] =>
    match goal with
    | [ H : ∀ (a : Message bool TMT B[T]) (b : Message bool TMT C[s]), _ |- _ ] =>
      destruct (H (V tt) unmarked);
      destruct (H (V tt) marked)
    end
  | [ s : SType |- _ ] =>
    match goal with
    | [ H : ∀ (a : Message bool TMT C[s]), _ |- _ ] =>
      destruct (H unmarked);
      destruct (H marked)
    end
  end
.

Ltac reduction_step :=
  intros; compute;
  repeat match goal with
  | [ |- Reduction _ _ (PNew (? _; _) (! _; _) ?D ?P) _ ] =>
    apply RStruct with (PNew _ _ (inverse_duality D) (fun a b => P b a))
  | [ |- Reduction _ _ (PNew (&{_}) (⊕{_}) ?D ?P) _ ] =>
    apply RStruct with (PNew _ _ (inverse_duality D) (fun a b => P b a))
  | [ |- Reduction _ _ (PNew _ _ ?D (fun a b => b?[m]; ?PB <|> a![?M]; ?PA)) _ ] =>
    apply RStruct with (PNew _ _ D (fun a b => a![M]; PA <|> b?[m]; PB))
  | [ |- Reduction _ _ (PNew _ _ ?D (fun a b => PBranch ?BB b ?PB <|> a◃?M; ?PA)) _ ] =>
    apply RStruct with (PNew _ _ D (fun a b => a◃M; PA <|> PBranch BB b PB))
  end;
  constructors
.
Hint Extern 1 (_ ⇒ _) => reduction_step.

Ltac big_step_reduction :=
  intros; compute; repeat (eapply RStep; reduction_step)
.
Hint Extern 1 (_ ⇒* _) => big_step_reduction.

Ltac linearity :=
  unfold Linear; simp linear in *; tauto
.
Hint Extern 1 (Linear _) => linearity.
Hint Extern 1 (~ (Linear _)) => linearity.

(******************************************)
(*          SUBJECT REDUCTION             *)
(******************************************)

Theorem congruence_linear {P Q} : Congruence _ _ P Q →
  (single_marked P → single_marked Q) /\ (linear P → linear Q).
Proof.
  intros PcQ.
  induction PcQ; split; simp linear in *; try linearity_hypotheses; try tauto.
  - dependent destruction c; destruct b; destruct m; simp linear in *.
    + tauto.
    + destruct b; simp linear; tauto.
    + destruct b; simp linear; tauto.
  - dependent destruction c; destruct b; destruct m; simp linear in *.
    + tauto.
    + destruct b; simp linear; tauto.
  - dependent destruction c;
      destruct b;
      destruct mt;
      simp linear in *;
      linearity_hypotheses;
      tauto.
  - dependent destruction c;
      destruct b;
      destruct mt;
      simp linear in *;
      linearity_hypotheses;
      tauto.
Qed.
Hint Resolve congruence_linear.

Lemma branches_linear {n} (i : Fin.t n) {xs : Vector.t SType n}
      {Ps : Forall (fun s => Message _ _ C[s] → Process _ _) xs} :
  (single_marked (PBranch Ps (C false)) → single_marked (nthForall Ps i (C false))) /\
  (linear (PBranch Ps (C false)) → single_marked (nthForall Ps i (C true))) /\
  (linear (PBranch Ps (C false)) → linear (nthForall Ps i (C false))).
Proof.
  induction i; dependent induction Ps; repeat split; intro H; simp linear in *.
  - destruct H.
    assumption.
  - destruct H.
    destruct H0.
    assumption.
  - destruct H.
    destruct H0.
    assumption.
  - destruct H.
    decompose [and] (IHi v Ps).
    auto.
  - destruct H.
    destruct H0.
    decompose [and] (IHi v Ps).
    auto.
  - destruct H.
    destruct H0.
    decompose [and] (IHi v Ps).
    auto.
Qed.
Hint Resolve branches_linear.

Theorem reduction_linear {P Q} : Reduction _ _ P Q →
  (single_marked P → single_marked Q) /\ (linear P → linear Q).
Proof.
  intro PrQ.
  induction PrQ; split; simp linear in *.
  - intro A; destruct A; (destruct m;
      [ destruct t; simp linear in *; tauto
      | destruct b; simp linear in *; tauto ]).
  - intro A.
    decompose [and or] A; try contradiction.
    destruct m;
      [ destruct t; simp linear in *; tauto
      | destruct b; simp linear in *; tauto ].
  - destruct (@branches_linear _ i rs Qs).
    intro A.
    decompose [and or] A; tauto.
  - decompose [and] (@branches_linear _ i rs Qs).
    intro A.
    decompose [and or] A; tauto.
  - linearity_hypotheses; tauto.
  - linearity_hypotheses; tauto.
  - tauto.
  - tauto.
  - destruct (congruence_linear H).
    tauto.
  - destruct (congruence_linear H).
    tauto.
Qed.
Hint Resolve reduction_linear.

Theorem subject_reduction P Q : P ⇒ Q → Linear P → Linear Q.
Proof.
  intros PrQ lP.
  refine (
      (match (P bool TMT fMT) as P'
             return linear P' → Reduction _ _ P' (Q bool TMT fMT) → linear (Q bool TMT fMT)
       with
       | _ => _
       end) lP (PrQ bool TMT fMT)).
  intros slP sPrQ.
  destruct (reduction_linear sPrQ) as [_ lPlQ].
  exact (lPlQ lP).
Qed.
Hint Resolve subject_reduction.

Theorem big_step_subject_reduction P Q : P ⇒* Q → Linear P → Linear Q.
Proof.
  intros PrQ lP.
  refine (
      (match (P bool TMT fMT) as P'
             return linear P' → RTReduction _ _ P' (Q bool TMT fMT) → linear (Q bool TMT fMT)
       with
       | _ => _
       end) lP (PrQ bool TMT fMT)).
  intros slP sPrQ.
  induction sPrQ.
  auto.
  destruct (reduction_linear H); auto.
Qed.
Hint Resolve big_step_subject_reduction.

(******************************************)
(*               EXAMPLES                 *)
(******************************************)

Example example1 : PProcess.
  refine
  ([υ]> (new i <- _, o <- _, _)
    (i?[m]; ![m]; ε) <|> (o![υ _ true]; ?[m]; ε)).
  auto.
Defined.
Print example1.

Example example2 : PProcess :=
  ([υ]> (new o <- ! B[bool] ; ? B[bool] ; ø, i <- ? B[bool] ; ! B[bool] ; ø, ltac:(auto))
    (o![υ _ true]; ?[m]; ε) <|> i?[m]; ![m]; ε).

Example congruent_example1 : example1 ≡ example2. auto. Qed.

Example example3 : PProcess :=
  ([υ]> (new o <- ? B[bool] ; ø, i <- ! B[bool] ; ø, ltac:(auto))
    (o?[m]; ε) <|> i![υ _ true]; ε).

Example reduction_example1 : example2 ⇒ example3. auto. Qed.

Example subject_reduction_example1 : example2 ⇒ example3 → Linear example2 → Linear example3.
eauto.
Qed.

Example example4 : PProcess :=
  ([υ]> (new i <- ! B[bool] ; ø, o <- ? B[bool] ; ø, ltac:(auto))
    (i![υ _ true]; ε <|> o?[m]; ε)).

Example congruent_example2 : example3 ≡ example4. auto. Qed.

Example example5 : PProcess :=
  ([υ]> (new i <- ø, o <- ø, Ends) (ε i <|> ε o)).

Example reduction_example2 : example4 ⇒ example5. auto. Qed.

Example big_step_reduction : example1 ⇒* example5. auto. Qed.

Example big_step_subject_reduction_example1
  : example1 ⇒* example5 → Linear example1 → Linear example5.
eauto.
Qed.

Example completion : Completes example1.
Proof.
  compute.
  exists example5.
  split.
  big_step_reduction.
  compute.
  tauto.
Qed.

Example channel_over_channel : PProcess :=
  [υ]>
    (new i <- ? C[ ! B[bool] ; ø ] ; ø, o <- ! C[ ! B[bool] ; ø ] ; ø, MLeft Ends)
    (new i' <- ? B[bool] ; ø, o' <- _, MLeft Ends)

    (i?[c]; fun a => ε a <|> c![υ _ true]; ε)
    <|>
    (o![o']; fun a => ε a <|> i'?[_]; ε)
.

Example channel_over_channel1 : PProcess :=
  [υ]>
    (new i' <- ? B[bool] ; ø, o' <- ! B[bool] ; ø, MLeft Ends)
    (new i <- ? C[ ! B[bool] ; ø ] ; ø, o <- ! C[ ! B[bool] ; ø ] ; ø, MLeft Ends)

    (i?[c]; fun a => c![υ _ true]; ε <|> ε a)
    <|>
    (o![o']; fun a => i'?[_]; ε <|> ε a)
.

Example congruent_example3: channel_over_channel ≡ channel_over_channel1. auto. Qed.

Example nonlinear_example : PProcess :=
  [υ]> (new i <- ? B[bool] ; ø, o <- ! B[bool] ; ø, MLeft Ends)

    (* Cheat the system by using the channel o twice *)
    i?[_]; ε <|> o![υ _ true]; (fun _ => o![υ _ true]; ε)
    .

Example linear_example1 : Linear example1. auto. Qed.

Example linear_channel_over_channel : Linear channel_over_channel. auto. Qed.

Example nonlinear_example1 : ~ (Linear nonlinear_example). auto. Qed.

Example branch_and_select : PProcess :=
  ([υ]> (new
           i <- &{ (! B[bool] ; ø) :: (? B[bool] ; ø) :: [] },
           o <- ⊕{ (? B[bool] ; ø) :: (! B[bool] ; ø) :: [] },
           ltac:(auto))
          i▹{(![υ _ true]; ε) ; (?[m]; ε)} <|> o◃Fin.F1; ?[_]; ε).
