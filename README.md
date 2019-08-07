This project requires [Coq 8.8.2][coq] and [Coq-Equations v1.2-8.8][equations].
They can both be installed via [opam][opam] or from source. If you happen to be
using the package manager Nix, you can launch a shell with both of them in
scope:

[equations]: https://github.com/mattam82/Coq-Equations/releases/tag/v1.2-8.8
[coq]: https://github.com/coq/coq/releases/tag/V8.8.2
[opam]: https://coq.inria.fr/opam-using.html

```
nix-shell --packages coq_8_8 coqPackages_8_8.equations
```

Once those two dependencies are in scope, this project can be compiled as
follows:

```
coq_makefile -f _CoqProject -o makefile
make
```

Alternatively, to step through the definitions and proofs, you can run `coqide
src/SessionTypes.v` and press `F6` or select `Compile -> Make`. You can then
interactively walk through the proofs with `Ctrl-Down` and `Ctrl-Up`.
