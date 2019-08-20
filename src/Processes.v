Require Import Forall.
Require Import Types.
Require Vectors.Vector.
Import Vector.VectorNotations.

Section Processes.
  Variable ST : Type.
  Variable MT : Type -> Type.

  Inductive Message : MType -> Type :=
  | V : forall {M : Type}, MT M -> Message B[M]
  | C : forall {S : SType}, ST -> Message C[S]
  .

  Arguments V [M].
  Arguments C [S].

  Inductive Process : Type :=

  | PNew
    : forall (s r : SType)
    , Duality s r
    -> (Message C[s] -> Message C[r] -> Process)
    -> Process

  | PInput
    : forall {m : MType} {s : SType}
    , (Message m -> Message C[s] -> Process)
    -> Message C[? m ; s]
    -> Process

  | POutput
    : forall {m : MType} {s : SType}
    , Message m
    -> (Message C[s] -> Process)
    -> Message C[! m ; s]
    -> Process

  | PBranch
    : forall {n : nat} {ss : Vector.t SType n}
    , Forall (fun s => Message C[s] -> Process) ss
    -> Message C[&{ss}]
    -> Process

  | PSelect
    : forall {n : nat} {ss : Vector.t SType n} (i : Fin.t n)
    , Message C[⊕{ss}]
    -> (Message C[ss[@i]] -> Process)
    -> Process

  | PComp : Process -> Process -> Process

  | PEnd : Message C[ø] -> Process
  .

  Reserved Notation "P ≡ Q" (no associativity, at level 80).
  Inductive Congruence : Process -> Process -> Prop :=
  | CCompCommutative {P Q} :
      PComp P Q ≡ PComp Q P

  | CCompAssociative {P Q R} :
      PComp (PComp P Q) R ≡ PComp P (PComp Q R)

  | CCompCongruent {P Q R S} :
      P ≡ Q -> R ≡ S -> PComp P R ≡ PComp Q S

  | CScopeExpansion {s r sDr P Q R} :
      (forall (a : Message C[s]) (b : Message C[r]), P a b ≡ Q a b) ->
      PComp (PNew s r sDr P) R ≡ PNew s r sDr (fun a b => PComp (Q a b) R)

  | CScopeCommutative {s r sDr s' r' sDr' P Q} :
      (forall (a : Message C[s]) (b : Message C[r]) (c : Message C[s']) (d : Message C[r']), P a b c d ≡ Q a b c d) ->
      PNew s r sDr (fun a b => PNew s' r' sDr' (fun c d => P a b c d)) ≡
      PNew s' r' sDr' (fun c d => PNew s r sDr (fun a b => Q a b c d))

  | CNewTypesCommutative {s r sDr P Q} :
      (forall (a : Message C[s]) (b : Message C[r]), P a b ≡ Q a b) ->
      PNew s r sDr (fun a b => P a b) ≡ PNew r s (duality_comm sDr) (fun b a => Q a b)

  | CNewCongruent {s r sDr P Q} :
      (forall (a : Message C[s]) (b : Message C[r]), P a b ≡  Q a b) ->
      PNew s r sDr P ≡ PNew s r sDr Q

  | COutputCongruent {mt st} {m : Message mt} {c : Message C[! mt; st]} {P Q} :
      (forall (a : Message C[st]), P a ≡ Q a) ->
      POutput m P c ≡ POutput m Q c

  | CInputCongruent {mt st} {c : Message C[? mt; st]} {P Q} :
      (forall (a : Message mt) (b : Message C[st]), P a b ≡ Q a b) ->
      PInput P c ≡ PInput Q c

  | CReflexive P :
      P ≡ P

  | CTransitive {P} Q {R} :
      P ≡ Q -> Q ≡ R -> P ≡ R

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
      (forall (a : Message C[s]) (b : Message C[r]), P a b ⇒ Q a b) ->
      (forall (sDr : Duality s r), PNew s r sDr P ⇒ PNew s r sDr Q)

  | RPar {P Q R} :
      P ⇒ Q -> PComp P R ⇒ PComp Q R

  | RStruct {P Q R} :
      P ≡ Q -> Q ⇒ R -> P ⇒ R

  where "P ⇒ Q" := (Reduction P Q)
  .

  Reserved Notation "P ⇒* Q" (at level 60).
  Inductive RTReduction : Process -> Process -> Prop :=
  | RRefl P : P ⇒* P
  | RStep P Q R : P ⇒ Q -> Q ⇒* R -> P ⇒* R
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
Definition ε {ST : Type} {MT: Type -> Type} : Message ST MT C[ø] -> Process ST MT:= PEnd ST MT.

Arguments V [ST MT M].
Arguments C [ST MT S].
Arguments PNew [ST MT].
Arguments PInput [ST MT m s].
Arguments POutput [ST MT m s].
Arguments PSelect [ST MT n ss].
Arguments PBranch [ST MT n ss].
Arguments PComp [ST MT].
Arguments PEnd [ST MT].
