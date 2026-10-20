## What changed

The original package theorem is assembled from three separate parts of its existing
source argument: normalized geometric and scalar operations, the clopen comparison
and coherence calculation, and the finite strict-tower identification. The assembly
constructs the refinement transformation as the actual adjunct of the prescribed
three-factor clopen map. It proves the coefficient square by the counit calculation,
naturality by naturality of this transformation, and commuting coefficient squares
from the coefficient cocycle. Shift compatibility of the square follows by whiskering
and composition, with the required functor associators inserted explicitly.

The existing interfaces are moved unchanged to `RingedRefinementData` and publicly
reexported by the item. This gives the three component statement modules a common
interface without an import cycle. `RingedRefinementConstruction` constructs the
coefficient compositor and refinement transpose. `CanonicalRingedRefinementShape`
constructs the pullback and clopen section. No data definition contains `sorry` and
no arbitrary witness from a mere existence theorem is used to define data.

## Proved and sorry left

Closed the original hole in `SheafOfModules.ringedRefinementCoefficientSquare` by
assembly. This is a decomposition, not a completed proof of the package existence.
Proved `CategoryTheory.refinement_coefficient_mate`, `canonicalShape`,
`canonicalCoefficients`, `canonicalRefinements`, `laws_of_clopen`, and
`shifts_of_generators`, including the coefficient-square and shift glue.

Three new named theorem holes remain:

- `SheafOfModules.RingedRefinement.ringedRefinementCore`, node
  `lem-pur-ringed-refinement-core` (source Steps 1--2 and 6).
- `SheafOfModules.RingedRefinement.ringedRefinementClopen`, node
  `lem-pur-ringed-refinement-clopen-laws` (source Steps 3--8).
- `SheafOfModules.RingedRefinement.ringedRefinementFinite`, node
  `lem-pur-ringed-refinement-finite-normalization` (source Step 10).

Thus one original hole is closed and three holes are added. Each component has its
complete source proof in its docstring and a matching DAG node. The item has zero
remaining textual holes; the new modules have three in total.

## No longer needed

No modules are pruned from the dependency closure. The direct proof-only imports
`Mathlib.Algebra.Category.Grp.FilteredColimits`,
`Mathlib.CategoryTheory.Abelian.FunctorCategory`, and
`Mathlib.CategoryTheory.Sites.Limits` are removed. The other former proof-only
imports move to the component module that needs them. The geometric constructor
uses `lem-weil-pbc-proper-open-section` directly; it does not directly use
`lem-cbc-strict-tower-proper-open-calculus`, which is still needed by the finite
normalization component. The item's former imports belong
to the unchanged interfaces or to the component calculations, so they remain in the
delivery's transitive imports. The generic mate lemma needs only Mathlib's adjunction
mate API. No flatness assumption, inverse of the coefficient mate, or detection of
derived morphism equality by evaluation is used.

## Where the brief, the DAG or earlier work was wrong

The earlier interrupted attempt left an obsolete report and incomplete shift glue.
Both are repaired. The core proof plan also distinguishes the invertible
coefficient identification after inverse image from the generally noninvertible
map into direct image. Strictly equal underlying composite functors need explicit
associators to compare their chosen shift structures. The source's numbered route
is retained, with the formal mate calculation and package assembly now made explicit.
The unchanged interfaces are factored only to make the independently sourced
component modules importable; their definition bodies and the target signature are
unchanged. No definition or proof was weakened to accommodate compilation.

## New nodes

`lem-pur-refinement-coefficient-mate` records the proved abstract counit calculation.
`lem-pur-ringed-refinement-formal-laws` records formal completion of the coefficient
laws and shifts. `lem-pur-ringed-refinement-core`,
`lem-pur-ringed-refinement-clopen-laws`, and
`lem-pur-ringed-refinement-finite-normalization` record the three separate source
arguments still to prove. `def-pur-ringed-refinement-data` records the unchanged
interface definitions; `def-pur-ringed-refinement-construction` records the actual
coefficient and refinement constructions; `def-pur-ringed-refinement-shape` records
the constructed geometric pullback and section.

Change record: `coord/changes/ringed-refinement-interfaces.md`.

Validation: all nine sandbox modules compile cleanly in import order.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
