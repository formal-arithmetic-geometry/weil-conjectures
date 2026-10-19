## What changed

Proved the three original theorems in `Sheaf.Paper.CompletedRlimFunctor` without
changing their statements or the public constructions. The computation theorem uses
the existing K-injective derivability instance. The properties theorem uses the
existing triangulated right-derived-functor instances and `Functor.rightDerivedUnique`.
The Roos theorem constructs the actual limit cone on a K-injective representative,
applies `derivedCategory_towerLimit_triangle`, and transports the triangle with its
specified first arrow. The proved private `completedRlimProjection_unit` checks the
universal-unit compatibility for each ordinary limit projection.

The exact-products import exposes general sheafification instances with unresolved
coefficient universes. Two private theorems specialize the already published sheafification and
locally-bijective proofs to universe t+1 and are registered only as local instances.
The broad `GrothendieckTopology.hasSheafify_of_essentiallySmall` instance is disabled
only inside individual declarations using scoped `attribute ... in` commands.
No new global instance or global instance removal is exported.
No public definition or signature is changed, and no arbitrary choice of a data
witness or adapted consumer is introduced. The only choices are universal products, the existing
K-injective equivalence, and a connecting map in a distinguished triangle.

Revalidated the retained proof against the current server library on 2026-10-19.
The single-file compile succeeds without warnings (5.6 seconds on the current
revalidation). The three new direct proof imports pass the import-direction check.

Updated `prop-weil-pbc-rlim-functoriality` proof fields to describe the actual route.
Added `coord/changes/CompletedRlimFunctorInstances.md` to document the scoped
universe-instance interface change required by Lean preflight; no consumers need adaptation.
The definition node `def-pur-completed-rlim-functor` is unchanged.

## Proved and sorry left

Closed the three original holes, with zero holes added and zero split off:

- `AlgebraicGeometry.Scheme.completedRlim_computation`.
- `AlgebraicGeometry.Scheme.completedRlim_properties`.
- `AlgebraicGeometry.Scheme.completedRlim_roos`.

All three belong to `prop-weil-pbc-rlim-functoriality`. No sorry remains in the module.
Existing named dependency theorems retain their own obligations; this delivery proves
from their published statements as required by stage 3.

## No longer needed

Removed these redundant direct proof imports:

- `Sheaf.Paper.AdicCoefficientDatum`: already public through CompletedDerivedInverseLimit.
- `Sheaf.CategoryTheory.KInjectiveBridge` and
  `WeilConjectures.CategoryTheory.KInjectiveBridge`: the existing derived-functor
  derivability API supplies the K-injective computation directly.
- `Mathlib.Algebra.Homology.Additive`: available through the retained APIs.
- `Mathlib.Algebra.Homology.CochainComplexPlus`: no bounded-below construction is used.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`: its etale-specific resolution alias
  is unnecessary for strict towers in an arbitrary abelian category.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: available through retained imports.
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitTower` and
  `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTower`: retired re-export
  and wrapper of the weaker existential limit-property theorem.
- `Mathlib.Algebra.Homology.Functor`: public through the retained tower-triangle API.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: available through retained APIs.
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic`: public through retained APIs.
- `Mathlib.CategoryTheory.Functor.OfSequence`: no explicit ofOpSequence comparison needed.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`: public through retained APIs.

The direct proof no longer uses `lem-weil-pbc-kinjective-hom-derived`: lifting
morphisms individually is encapsulated in the existing universal derived functor.
It no longer uses `prop-weil-pbc-derived-inverse-limit-computation` or its
`WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTower` wrapper:
that theorem forgets the specified first map, whereas the proved descendant
`lem-weil-derived-limit-tower-core-property-triangle` retains exactly the projection
family needed here. `def-weil-pbc-kinjective-resolutions` is not needed as a proof
dependency: its etale-specific alias is replaced by Mathlib K-injectivity for strict
towers. `def-weil-size-convention` imposes universes, not an extra Lean proof;
the proof states the existing coefficient and site universe parameters explicitly.
These nodes can still be needed elsewhere; no global deletion is asserted.
The unit's realized statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original general-tower computation dependency returns `IsDerivedLimit`, which
forgets the first arrow. It cannot by itself establish the published
`completedRlim_roos` conclusion with `completedRlimRoosProjection`. The existing
canonical localized triangle theorem is the suitable stronger interface, and the
remaining projection comparison is now proved explicitly.

The blueprint sentence about arbitrary levelwise homotopy equivalences is not used
to choose functorial cones. All maps come from the actual total right-derived functor
of strict inverse limit. The universe sizes and all three public theorem statements
are unchanged, including zero coefficient rings and arbitrary unbounded objects.

The proof uses `lem-weil-proetale-countable-products-exact` as a tool to establish
CountableAB4Star for completed coefficient module sheaves; no etale-only exactness
claim or bounded-below substitute is made. The already recorded
`prop-pur-kinjective-resolutions-exist` tool supplies enough injectives for the
coefficient category. No new nodes are needed; the scoped instance changes are documented in
`coord/changes/CompletedRlimFunctorInstances.md`.

The resumed session rechecked the retained proof against current sources. The
module compiled cleanly in 5.6 seconds. The required dry run passed compilation,
axiom probing and preflight (commit aa407c64f9), with CODEX review classification
for the changed node and file-local elaboration commands. The change record
compares the delivered setup with the repository baseline.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
