## What changed

Partial proof delivery for `Sheaf.Paper.AcyclicHypercoverPullbackNormalization`.
The row-resolution maps are identified with the already proved single-sheaf total
isomorphism in `ProEtaleNormalizedHypercoverDescent`. Naturality of total injections
then proves their differential and coefficient-map identities.

The actual adjunction unit and sheaf restrictions prove the differential,
coefficient and refinement identities degree by degree. Negative source degrees
are zero objects. Composition uses the existing `HypercoverUnit.restriction_comp_section`
statement. Comparison refinement follows by cancelling the localized resolution
map in the normalized augmentation square.

Only the item module and its node are changed. Public statements, constructions
and public imports retain their existing signatures and definitions. All added
helpers are private and proved. The node records the component argument.

Validation: the remote single-file compile succeeded in 46.2 seconds. Its sole
long-line warning was corrected by wrapping the line before delivery.

## Proved and sorry left

Eight of eleven existing holes closed, all in namespace
`AlgebraicGeometry.Scheme.AcyclicHypercover`:

- `rowResolutionComponent_comm`
- `rowResolution_single_isIso`
- `rowResolution_eq_total_map`
- `restrictionComponent_comm`
- `restriction_naturality`
- `comparison_refinement`
- `restriction_refinement`
- `restriction_comp`

Three existing holes remain, under node
`lem-sfb-acyclic-hypercover-pullback-normalization`:

- `AlgebraicGeometry.Scheme.AcyclicHypercover.descent`
- `AlgebraicGeometry.Scheme.AcyclicHypercover.pullback_normalization`
- `AlgebraicGeometry.Scheme.AcyclicHypercover.derivedSectionPullback_comp`

No holes added and no statements split off. Comparison refinement uses the
existing `descent` normalization theorem; composition uses the existing stated
cross-site section lemma. This is a partial realization, not a claim that the
remaining derived comparison statements or the target closure are sorry-free.

## No longer needed

Removed these direct proof imports:

- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties`
- `Mathlib.CategoryTheory.Sites.EpiMono`
- `Mathlib.CategoryTheory.Sites.LocallySurjective`
- `Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentationRing`
- `Sheaf.Algebra.Homology.BoundedBelowAugmentation`
- `Sheaf.Algebra.Homology.BoundedBelowTotalComparison`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`

The two stated parent proof dependencies are both retained and explicitly
imported. Their own lower dependencies remain needed transitively; no DAG node
or source-library declaration is withdrawn, and no whole module is claimed
pruned from the target closure. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The item duplicates the row, total and evaluation
constructions in the subsequently stated single-site module. Its `single_sheaf`
component formula supplies the shortest proof of the row-resolution identities.

The three remaining holes require further assembly of the canonical derived
models: the item's actual `rightDerivedFunctor` and terminal-object section
comparison differ syntactically from the single-site dependency's universal
right-derived construction and the cross-site dependency's base-changed
augmentation object. Their normalization and composition identifications have
not been completed in this partial delivery.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
