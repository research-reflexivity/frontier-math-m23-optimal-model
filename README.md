# A minimal-degree (23,4)-model and an arithmetic progression of \(M_{23}\)-polynomials

Companion certificates for two papers by François Le Lay (Reflexivity):

- [A minimal-degree (23,4)-model and an arithmetic progression of Mathieu \(M_{23}\)-polynomials](paper/LeLay_M23_Optimal_Model_2026-08-20.pdf)
- [A second arithmetic progression of Mathieu \(M_{23}\)-polynomials](paper/LeLay_M23_Progression_85_Draft_2026-08-20.pdf)

This repository is
<https://github.com/research-reflexivity/frontier-math-m23-optimal-model>.

Huang--Jackson--Lee--Poonen--Pries--Zhang constructed a regular
\(M_{23}\)-extension of \(\mathbf Q(t)\) by a bidegree-\((23,8)\)
equation, and observed that the same cover admits a degree-\(4\)
function over \(\mathbf Q\), and that no function of degree at most \(3\)
exists over \(\mathbf Q\). In the published notation their integral source
polynomial is \(F\in\mathbf Z[T,V]\). Writing \(D=T^2+23\), its monic
normalization is \(\widehat F=D^{-4}F\in\mathbf Q(T)[V]\). The upstream GP
program calls these two objects `Fint` and `F`, respectively; the generated GP
input records that translation and uses `F` and `Fhat`, respectively, to match
the paper. This repository
supplies that equation
\(P(T,W)\in\mathbf Z[T,W]\), three exact model certificates in Singular,
SageMath, and Magma, a Lean 4 certificate for irreducibility of the mod-31
model, and the PARI/GP certificates for the paper’s arithmetic
claims: the valuations at the two ramification
points, the explicit specialization at \(t=2\), the uniform two-prime
certificate that every primitive part \(P(t,x)\) with
\(t\equiv 2\pmod{319}\) has Galois group \(M_{23}\), and the
controlled-ramification witness \(t=3830\).

The short companion note proves a second uniform progression for the same
regular cover. Every primitive specialization of the published
bidegree-\((23,8)\) equation with \(t\equiv83\pmod{85}\) has Galois group
\(M_{23}\). Its exact certificate freezes factor degrees
\((1,2,4,8,8)\) modulo \(5\) and an irreducible degree-\(23\) reduction
modulo \(17\). This is a second certificate for the same cover, not an
independent \(M_{23}\)-family.

There are no GAP programs. The model certificates prove the exact identity
giving \(\mathbf Q(T,W)=\mathbf Q(T,V)\) and irreducibility modulo \(31\).
The Magma certificate is self-contained, is deterministically generated from
the canonical JSON tables, and was run successfully with Magma V2.29-9; its
recorded output is in
[`verification/magma_verification_summary.json`](verification/magma_verification_summary.json).

## Reproduce

For the arithmetic certificates, you need
[PARI/GP](https://pari.math.u-bordeaux.fr/) on `PATH` as `gp` (developed
against 2.17.4). Override the executable if needed:

```sh
make verify GP=/path/to/gp
```

To run only the new progression certificate:

```sh
make verify-progression-85
```

The three independent exact-model paths can be run separately:

```sh
make verify-model-singular
make verify-model-sage
make verify-model-magma
```

The formal mod-31 irreducibility certificate is separate from those
birational-model checks:

```sh
make verify-lean
```

The first two require Singular 4.4 and SageMath 10.9 respectively. The third
requires a licensed Magma 2.29 executable; Magma is optional and is not
bundled. The Lean project pins Lean and mathlib 4.32.1 and requires `lake`
(normally installed through `elan`). It proves primitivity, degree preservation
at \(T=7\), irreducibility of \(P(7,W)\), and the specialization lift to
\(P(T,W)\). See [`verification/lean/README.md`](verification/lean/README.md).
`make verify-data` checks the published data and verification-summary hashes.
If every runtime is available, `make verify-all` runs the complete suite.
Executable names can be overridden with `GP=`, `SAGE=`, `MAGMA=`, `SINGULAR=`,
`LAKE=`, and `PYTHON=`.

The ramified-witness certificate requests a 4 GB PARI stack and computes
two degree-23 field discriminants.

## Layout

- `paper/` — the two paper PDFs
- `verification/` — Singular, SageMath, Magma, Lean, PARI/GP, and Python
  certificates, with machine-readable run summaries
- `data/` — canonical JSON coefficient tables and generated Singular/PARI
  inputs for HJLPPZ's integral source polynomial \(F\), the primitive
  \((23,4)\) equation, and its arithmetic witnesses
- `scripts/` — deterministic Magma-certificate generation and the adjoint
  reconstruction dependency
- `CHECKSUMS.sha256` — fixity manifest for the exact data and core summaries

## Licensing

Copyright 2026 Reflexivity, Inc.

- Software and scripts: [Apache License 2.0](LICENSE)
- This README, third-party notices, and the paper PDFs: [CC BY-NC-SA 4.0](LICENSE-CC-BY-NC-SA-4.0)
- Original generated data in `data/`: [CC0 1.0](LICENSE-CC0-1.0), to
  the extent Reflexivity holds the relevant rights

These licenses do not relicense third-party materials.  See
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

## Primary source

X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, and S. Zhang,
*The Mathieu group \(M_{23}\) is a Galois group over \(\mathbf Q\)*,
[arXiv:2608.08538](https://arxiv.org/abs/2608.08538) (2026), especially
Remark 3.4.
