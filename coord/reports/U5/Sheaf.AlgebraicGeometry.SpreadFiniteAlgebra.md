## What changed

In `Sheaf.AlgebraicGeometry.SpreadFiniteAlgebra`, placed the existing product theorem
before the algebra-only theorem and proved `AlgebraicGeometry.spread_finite_algebra`
from `AlgebraicGeometry.spread_finite_algebra_product` using its singleton product.
Constructed the limiting identity fan explicitly, applied the stronger statement,
and retained exactly the required algebra model and pushout. Every existing
signature and visibility is unchanged. The node records this corollary after its
unchanged nine-step plan for the product theorem.

Removed eight redundant proof imports: the five compatibility modules listed below
already re-export canonical modules imported directly, and the other three imports
are supplied by unchanged public imports. No public import changed.

Validation: the singleton-fan construction and corollary compiled via `lcompile.py`.
The final module and the required delivery checks are run again after import cleanup.
This is a partial proof delivery, not a proof of the stronger product theorem.

## Proved and sorry left

Closed 1 of the original 2 holes:
`AlgebraicGeometry.spread_finite_algebra`
(node `lem-fin-spread-finite-algebra`). This proof uses the existing stronger
product assertion, which remains open; it does not establish algebra spreading
independently of that assertion.

One original hole remains, unchanged:
`AlgebraicGeometry.spread_finite_algebra_product`
(node `lem-fin-spread-finite-algebra`). Its existing docstring and node give the
module descent, multiplication/unit and idempotent descent, eventual algebra-law
identities and product reconstruction still to be formalized.

Added 0 holes and split off 0 statements. No new module or assumption was added.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.CoherentLocalFinitePresentation`
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
- `Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`
- `Sheaf.AlgebraicGeometry.ModulePullbackTensor`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf`

The first five are retired re-export wrappers; the corresponding five canonical
`WeilConjectures` modules remain imported directly. ProjectiveSpace and Proper
are publicly imported by the unchanged public Projective import; CommAlgebraSheaf
is publicly re-exported by the unchanged public Sheaf CommAlgebraSheaf import.
No mathematical dependency node is pruned: all original proof dependencies remain
in the plan for the still-open product theorem. No claim is made that another
importer cannot also reach a removed compatibility wrapper.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The module need not implement two independent spreading
arguments: its product assertion already includes the algebra-only conclusion.
The one-factor identity fan works for empty schemes and the zero algebra as well.
The unit record has no realized statement or steps bypassed by this specialization.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
