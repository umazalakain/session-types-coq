# Links

- HOAS: http://adam.chlipala.net/cpdt/html/Hoas.html
- Certified programming with dependent types: http://adam.chlipala.net/cpdt/
- Software Foundations: https://softwarefoundations.cis.upenn.edu/
- https://www.um.edu.mt/projects/behapi/behapi-workshop-etaps-2019/

# Notes about Coq

- `Prop` is impredicative.
    A definition is said to be impredicative if it generalises over the totality
    to which the the entity being defined belongs.

    Otherwise said, a statement of the form `∀ A : Prop, P A` can be
    instantiated by itself: if `∀ A : Prop, P A` is provable, then `P (∀ A :
    Prop, P A)` is.

- `Set` is predicative.
    It lays at the bottom of the type hierarchy.

- `Type` is stratified, but its universe level is hidden from the user.

- All proofs are provided via tactics. Tactics are applied in an imperative
  style. Some tactics map to pattern matching, but pattern matching on dependent
  types requires overhead.

- Invariants are not carried through datatypes. Instead proofs and data are
  split.

- Many of the tactics are extremely powerful.

- Coq has a minimal kernel to which everything compiles to.

- Coq does not support induction-recursion.

