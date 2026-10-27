## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_finite_surjective_normal`
in `Sheaf.AlgebraicGeometry.FiniteNormalAmpleDescent`, with its signature unchanged.
Added private proof imports of `Sheaf.AlgebraicGeometry.NormalIntegralFiniteSheafNorm`
and `Sheaf.AlgebraicGeometry.FiniteNormInvertibleSections`.

The proof implements all seven steps of the existing DAG plan. It constructs the
reduced closed subscheme on the closure of a point over the generic point of the
target, proves it integral using the closed embedding, and proves its finite map
surjective because its closed image contains the generic point. It restricts the
ample invertible module, applies the existing sheaf norm and norm-section
theorems, and proves compactness and the affine section-neighbourhood condition
on the target. The same norm module is used for every point and tensor power.
No signatures, definitions, public imports, other modules, or DAG routes changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_finite_surjective_normal`
(node `lem-sfb-finite-normal-ample-descent`).

No holes remain in the item; no holes were added or split off. This is a proof
from the existing stated dependencies, including the still-unproved norm and
restriction theorems, rather than an assertion that their transitive proofs are
complete.

## No longer needed

None. Every original proof dependency remains used, and no import was removed.
The two norm modules were not originally imported despite being proof dependencies;
they are now imported privately. No module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The DAG's seven-step proof fits the
existing declarations. Compactness is obtained by Mathlib's continuous-surjection
lemma, implementing the open-cover argument in step 4. The existing integral
scheme hypothesis excludes an empty target; no nonemptiness hypothesis on the
source is added, since a point over the target's generic point is supplied by
surjectivity.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
