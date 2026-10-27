## What changed

Filled `AlgebraicGeometry.Scheme.integralConstructible_hom_sums` without changing its
signature or public imports. Shift the given family by q, apply the existing proved
bounded-below RHom coproduct comparison and degree-zero module homology, then transport
the colimit through the proved natural global-Hom comparison. Three proved private
helpers identify final-object evaluation with unit-module Hom and derive that natural
comparison after exact scalar forgetting. Mathlib's additive universe lift bridges the
cohomology and derived-morphism universes. Reflection of module colimits identifies the
final comparison with exactly the existing DirectSum.toModule map.

The item's Lean module and existing DAG proof record are changed; one new node records
an existing proved source-library comparison without changing that source module. The proof
works uniformly for an empty index type, negative q, arbitrary integer lower bounds,
and the zero/empty-scheme cases. No scalar-linearity assertion for an arbitrarily chosen
additive equivalence is needed: the displayed comparison is already A-linear, and
forgetting A reflects colimits.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.Scheme.integralConstructible_hom_sums`
(node `lem-weil-pbc-integral-constructible-hom-sums`). Added zero holes; split off zero
statements. No sorry remains in the item or is added elsewhere. Single-file compilation
passed in 12.7 seconds. An explicit axiom print reports propext, Classical.choice,
Quot.sound and transitive sorryAx from existing library dependencies; this delivery
closes the item's hole and does not claim to remove all downstream obligations.

## No longer needed

Removed the private imports `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`
and `Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel`. Their respective nodes
`lem-sf-ringed-derived-closed-symmetric-monoidal` and
`lem-sfb-derived-internal-hom-sections-model` are no longer direct proof dependencies,
and their obsolete top-level tool-use entries are removed. The proved natural
`lem-pur-rhom-global-sections` comparison replaces both direct uses. They may remain
transitive dependencies of that existing comparison; no library declaration or module
is withdrawn. Existing public imports are preserved. The new direct use of
`lem-pur-rhom-global-sections` is as a generic Hom/hypercohomology tool, and
`def-sfb-exact-derived-cohomology-comparison` is its exact-forgetting construction;
these do not replace a proper-base-change unit step. Any new off-unit tool approval
is left to the maintainer; no such approval is added by this delivery.

## Where the brief, the DAG or earlier work was wrong

The old step 3's all-degree additive equivalences did not themselves expose the
needed naturality for arbitrary derived morphisms or the scalar-valued-section bridge.
The existing `rhom_global_sectionsOfUniverses` theorem does expose derived naturality
in degree zero. Shifting the entire family first makes that proved interface suffice.
The bridge between evaluation-valued scalar sections and unit-module Hom is proved
explicitly, and exact postcomposition with scalar forgetting is handled by the existing
source-library right-derived composition comparison. Exact forgetting/cohomology uses
the existing normalized comparison definition node.

The rework row records a historical quarantine due to ProjectiveLineGenusZero. The
item source is currently present and was copied intact before proof work. No archived
module is deleted or treated as withdrawn, and no target, definition or public
signature is altered.

Delivery-service observation: three `deliver3.py` attempts each waited 50 minutes
before returning exit 75, `DELIVERY BUSY: 6 deliveries are running on this machine`.
None obtained a priority slot or pushed anything. The proved packet is retained intact. No launcher script or queue setting was changed.

## New nodes

`lem-pbc-right-derived-exact-postcomposition` attaches the existing proved
`CategoryTheory.Functor.rightDerivedFunctorCompMapDerivedCategoryIso` and records
its arbitrary additive first factor and exact second factor, including independent
derived universes and K-injective resolutions only on the source. It adds no Lean
module or hole. Searches of the entire blueprint for “right derived” and “exact
functor” and all DAG Lean attachments found no existing node for this comparison;
`def-sfb-right-derived-exact` concerns an exact functor itself, and
`lem-fin-kinjective-derived-composition` instead requires the first factor to
preserve K-injectives. LeanSearch, LeanFinder, Loogle and Mathlib source searches
are recorded in the new node. The ancestor and unit route are preserved.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
