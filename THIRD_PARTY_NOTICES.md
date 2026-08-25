# Third-party notices

The repository's Apache-2.0, CC BY-NC-SA 4.0, and CC0 declarations apply only
to rights held by Reflexivity, Inc. They do not relicense third-party
materials.

## Computational dependencies

The certificates invoke SageMath, Singular, and PARI/GP as external runtime
dependencies. The reference environment uses SageMath 10.9, Singular
4.4.1-p2, and PARI/GP 2.17.4. These programs are not bundled in this
repository.

An optional independent certificate invokes Magma as an external dependency.
It was run against Magma 2.29-9 and is not part of the default PARI/GP
verification target. Magma is not bundled in this repository and is
distributed separately by the Computational Algebra Group at the University
of Sydney.

- SageMath: https://www.sagemath.org/
- SageMath licensing: https://doc.sagemath.org/html/en/reference/spkg/sage.html
- Singular: https://www.singular.uni-kl.de/
- Singular licensing: https://github.com/Singular/Singular/blob/master/COPYING
- PARI/GP: https://pari.math.u-bordeaux.fr/
- PARI/GP licensing: https://pari.math.u-bordeaux.fr/faq.html#license
- Magma: https://magma.maths.usyd.edu.au/magma/
- Magma ordering and distribution: https://magma.maths.usyd.edu.au/magma/ordering/
- Lean: https://lean-lang.org/
- Lean licensing: https://github.com/leanprover/lean4/blob/master/LICENSE
- mathlib: https://github.com/leanprover-community/mathlib4
- mathlib licensing: https://github.com/leanprover-community/mathlib4/blob/master/LICENSE

SageMath and its components remain under the licenses identified by the
SageMath project. Singular and PARI/GP are distributed under the GNU General
Public License; consult the cited release materials for the controlling
terms. The dependency-free companion verifiers and certificate generators use
Python 3.14.6 and its standard library; Python is distributed under the Python
Software Foundation License.

The formal irreducibility certificate invokes Lean and mathlib as external
build dependencies. Exact revisions are pinned in `verification/lean`; neither
dependency is bundled in the tracked repository.

- Python: https://www.python.org/psf/license/

## Primary mathematical source

The regular \(M_{23}\)-extension, published bidegree-\((23,8)\) equation,
and source theorem are due to:

X. Huang, B. Jackson, K.-H. Lee, B. Poonen, R. Pries, and S. Zhang,
*The Mathieu group \(M_{23}\) is a Galois group over
\(\mathbf Q\)*, arXiv:2608.08538 (2026).

The authors' data repository is:

https://github.com/shaowuz/m23isgalois

At the time this notice was prepared, that external repository did not
provide an explicit software license. No license grant for its source
code is implied here. Before copying or redistributing any upstream
implementation, obtain permission or an explicit license from its
copyright holders.

The exact integral coefficient table in `data/Fint_coefficients_Z.gp`
represents the polynomial denoted `F` in the published paper and `Fint` in the
upstream GP program. The generated file uses `F` for this integral polynomial
and `Fhat` for its monic normalization, matching the accompanying paper. The
CC0 dedication covers only rights held by
Reflexivity and does not assert ownership of the underlying published equation
or of uncopyrightable mathematical facts.
