## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleRingModule_closed_essImage_iff_and_unit_isIso`
without changing its signature. Added two fully proved private helpers for the natural
coefficient/direct-image comparison and reflection of zero objects by tensor extension
along a coefficient isomorphism. The proof uses the existing ringed localization sequence,
then Mathlib's fully-faithful adjunction criterion for the actual canonical unit.
Updated the existing node's proof to match this argument; all declared dependencies remain used.

Replaced the public finite-coefficient direct-image import with the public
`Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction` import actually required
by the statement. Change record:
`coord/changes/T7-proEtaleClosedEssentialImage-imports.md`.
Added proof-only imports of Mathlib's fully-faithful adjunction API and the existing private
scalar-transport API via `import all Sheaf.AlgebraicGeometry.ProEtaleOperations`.

Validation: the item compiles through lcompile.py. The two unchanged direct consumers
both compiled unchanged against the narrowed interface (4.5 s and 5.1 s);
the item compiled in 6.6 s. Consumer copies were removed from the delivery sandbox
after validation, so only the assigned module is delivered. The proof uses
no finiteness, constancy, qcqs, boundedness, or nonzero-ring hypothesis. Empty schemes,
the zero ring sheaf, and either empty complementary part are covered by the same zero-object
and adjunction argument. Searches: LeanFinder for the support/unit criterion found only
unrelated generic/Zariski results; Loogle for essImage/unit and ShortExact/isIso located
the generic Mathlib criteria; grep and source reading confirmed their precise signatures.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.proEtaleRingModule_closed_essImage_iff_and_unit_isIso`
(node `lem-exc-proetale-closed-essential-image`).
Added 0 holes; split off 0 statements. No sorry remains in the item or is added elsewhere.
The two private helpers are fully proved.

## No longer needed

Removed import: `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`.
Its finite-coefficient naturality, direct-image additivity, K-injective-resolution and
coefficient-realization equivalence results are unnecessary for this arbitrary-ring-sheaf
support criterion. They may still be reached through other library routes; no global
module withdrawal is claimed.

No declared proof dependency or approved tool use is pruned: the proof still uses the
ringed localization theorem, ordinary coefficient operations, the module-sheaf category,
exactness, and the abelian-category criterion. The blueprint's older dependencies
`lem-exc-closed-localization`, `lem-exc-open-closed-detection`,
`lem-exc-proetale-closed-fully-faithful`, and
`prop-weil-pbc-proetale-constant-exact` are not imported for this proof; their needed
geometric input is already supplied by the declared ringed-localization dependency.
No explicit unit-comparison calculation or additional geometric lemma is needed: full
faithfulness and Mathlib's criterion apply directly to the specified canonical adjunction.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or hypothesis was wrong. The original public finite-coefficient
import was unnecessarily broad. The node's detailed manual unit comparison can be replaced
by Mathlib's criterion applied to the actual adjunction after deriving full faithfulness
from the already supplied closed counit. This stays within the existing unit route.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
