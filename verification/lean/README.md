# Lean certificate for irreducibility modulo 31

This project formally proves, for the canonical polynomial read from
`data/modular/f4_mod_31.json`:

1. `P_primitive`: `P(T,W)` is primitive as a polynomial in `W` over
   `F_31[T]`;
2. `specialization_preserves_W_degree`: evaluation at `T = 7` preserves its
   `W`-degree (both degrees are 23);
3. `p7_irreducible`: `P(7,W)` is irreducible over `F_31`;
4. `P_irreducible`: the proved specialization lemma applies and concludes
   that `P(T,W)` is irreducible in `F_31[T][W]`.

The concrete univariate proof uses the prime-degree Frobenius criterion. The
generated data contain 23 quotient identities for successive 31-power
reductions and a Bezout identity with `W^31 - W`. A second small Bezout identity
proves primitivity. `M23Certificate.Coefficients` proves the reflection lemmas
that transport the executable coefficient-list checks into mathlib
polynomials.

## Run

Install [elan](https://github.com/leanprover/elan), then from the repository
root run:

```sh
make verify-lean
```

The toolchain and dependency revisions are pinned by `lean-toolchain` and
`lake-manifest.json`. The first run downloads the pinned mathlib cache. To use a
non-default Lake executable, run `make verify-lean LAKE=/path/to/lake`.

The generated witness file must agree byte-for-byte with the canonical JSON;
the Make target checks this before compiling. Regenerate it only after an
intentional source-data change:

```sh
python3 scripts/emit_lean_certificate_data.py
```

## Trust boundary

There are no `sorry` declarations and no Singular, SageMath, Magma, or PARI/GP
calls in the proof. The finite computations use Lean's kernel-reduced `decide`,
not `native_decide`. `M23Certificate/Main.lean` prints the axiom dependencies
of every exported result; a successful build reports only mathlib's standard
`propext`, `Classical.choice`, and `Quot.sound` foundations.

The Lean certificate proves irreducibility of the published mod-31 polynomial.
It does not replace the separate Singular, SageMath, or Magma certificates for
the birational model identity and geometric checks.
