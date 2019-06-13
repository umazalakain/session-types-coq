Require Import Lists.List.
Import ListNotations.
Require Import Sorting.Permutation.

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

Definition Linear (p : FProcess) := let (created, used) := annotate 0 (p _ _ (fun _ _ => V _ tt))
                                    in Permutation created used.
