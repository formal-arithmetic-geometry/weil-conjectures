## What changed

Constructed the rank-one exterior Koszul coordinates in degrees -1 and 0. Proved that all other terms vanish, the differential is multiplication by a^(m+1), the transitions have components (a,1), and the exterior degree-zero unit is the inverse zero-degree coordinate map. Constructed the resulting complex isomorphisms using the two-term-complex universal property, with transition and unit normalization. Scalar-power compatibility is proved by induction using composition of multiplication maps.

Added a proved module-only coefficient normalization theorem. Its proof composes the normalized tensor/restriction adjunction with constant-module sheafification and the regular-module/sections equivalence. Yoneda proves the specified completed unit invertible; adjunction naturality proves scalar compatibility. The inverse transported unit is constructed sectionwise from the forward completed coefficient-ring isomorphism.

Updated the item's proof route and dependencies and added the coefficient-normalization node. Existing statement signatures and definitions were not changed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Scheme.negativeKoszulFactorRealization`: 1 of 1 original holes closed. Added 0 holes and split off 0 unproved statements. The new theorem `AlgebraicGeometry.Scheme.completedRealizationRegular` is proved. No `sorry` remains in either delivered module.

Validation: `lcompile.py --all` compiled both complete modules: `WeilCompletedRealizationRegular` in 5.6 seconds and `WeilNegativeKoszulFactorRealization` in 18.1 seconds. Static checks confirmed the original item signature is verbatim, the new node statement matches its Lean declaration, and both modules have no holes or lines over 100 characters. Temporary profiling options and diagnostic commands were removed.

## No longer needed

None. All original declared dependencies remain used for the actual coefficient functor, exterior coordinates, negative two-term model, transitions, and prescribed unit. No module is withdrawn. The only added proof imports are the proved coefficient-normalization module and the Mathlib exterior-basis and one-coordinate Finsupp APIs.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement defect was found. The coefficient-normalization step of the original plan was not separately stated; it is now a proved theorem about modules and scalars, rather than a further Koszul comparison obligation. The proof covers the zero ring and empty site: it uses only module-basis, unit, adjunction, and ring-isomorphism identities, with no nonzero or nonempty hypotheses.

## New nodes

`lem-weil-pbc-completed-realization-regular`, in `Sheaf.Paper.WeilCompletedRealizationRegular`, states and proves invertibility of the specified realized regular-module unit and its compatibility with multiplication by each scalar. It is strictly below the complex comparison: it contains no complexes, transition systems, exterior coordinates, or basis-unit conclusions. No change record is needed because no existing definition or statement was changed.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
