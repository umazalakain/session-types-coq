# Links

- Type systems for concurrent programs, Naoki kobayashi
- Session type subtyping, Simon Gay, Malcom Hol 2015
- Coq:
    - Oregon Programming Languages Summer School (OPLSS) 2011.
    - HOAS: http://adam.chlipala.net/cpdt/html/Hoas.html
    - Certified programming with dependent types: http://adam.chlipala.net/cpdt/
    - Software Foundations: https://softwarefoundations.cis.upenn.edu/
- Session types:
    - https://www.di.fc.ul.pt/~vv/papers/vasconcelos_fundamental-sessions.pdf
    - https://www.um.edu.mt/projects/behapi/behapi-workshop-etaps-2019/
    - http://groups.inf.ed.ac.uk/abcd/meeting-january2014/ornela-dardha.pdf
- Linearity:
    - https://www.cs.cmu.edu/~iliano/projects/metaCLF2/inc/dl/papers/lsfa17.pdf
    - https://jpaykin.github.io/papers/pz_linearity_monad_2017.pdf
    - https://www.cis.upenn.edu/~rrand/qpl_2017.pdf
    - http://www.cs.nuim.ie/~jpower/Research/Papers/1999/power-tphols99.pdf
    - https://repository.upenn.edu/cgi/viewcontent.cgi?article=4538&context=edissertations

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

# Linearity

- With continuation passing, channels are required to be linear.

- We do HOAS, and Coq does not support linearity.

- We must be able to traverse a process and check the creation and usage of
  channels.

- To do so we can use the parametricity of HOAS.

- Channels can be sent over channels. To properly check the linearity of these
  channels sent over channels, we would need to actually evaluate the process. A
  way of avoiding that is to mark a channel as used when it's sent as a message.
  When it is received as a message, we make a new created mark. This way we
  avoid evaluation, at the cost of treating the same channel as two different
  channels.

- All messages cannot be treated equally: we need to know whether they are
  channels or plain messages.

# Evaluation

- Evaluation requires finding two parallel processes with opposite channels
