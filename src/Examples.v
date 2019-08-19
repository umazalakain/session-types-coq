Require Vectors.Vector.
Import Vector.VectorNotations.

Require Import Forall.
Require Import Types.
Require Import Processes.
Require Import Linearity.
Require Import Generalisation.
Require Import Tactics.

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

Example subject_reduction_example1 : example2 ⇒ example3 -> Linear example2 -> Linear example3.
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
  : example1 ⇒* example5 -> Linear example1 -> Linear example5.
eauto.
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

Example congruent_example3 : channel_over_channel ≡ channel_over_channel1. auto. Qed.

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
