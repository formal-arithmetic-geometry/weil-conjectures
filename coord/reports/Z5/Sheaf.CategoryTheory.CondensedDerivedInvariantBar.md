## What changed

Proved `CategoryTheory.CondensedBar.condensed_derived_invariant_bar` from the existing
`condensed_bar_scalar_resolution_comparison`. Its `ScalarResolutionAssertion` already
supplies the identical action-abelian structures, Grothendieck structures, standard
derived categories, and coefficient-indexed `Model`s used by `Assertion`. Retain these
witnesses. For each ring map retain its `ScalarModel`, and map the nonempty
`ScalarResolutionComparison` through its `computation` projection. This retains all
ordinary bar computation, augmentation normalization, naturality, and scalar clauses.
There is no new definition, choice of an undetermined object, weakened signature,
new lemma, or change to the unit route.

Replaced the private proof imports with the single private import
`Sheaf.CategoryTheory.CondensedBarScalarResolutionComparison`. The public import and
all existing declaration signatures and docstrings are unchanged. Updated the item's
DAG proof, proof dependencies and proof origin to the actual projection argument.

The current live item exists; it is the restoration source used here. The historical
quarantine row was checked; no archive is withdrawn or deleted. There is no current
return entry for this item in `coord/returns/Z5.md`.

## Proved and sorry left

Closed one existing hole:
`CategoryTheory.CondensedBar.condensed_derived_invariant_bar`
(node `lem-sfb-condensed-derived-invariant-bar`).

Item holes: 1 before, 0 after. Added holes: 0. Split-off theorems: 0.
The existing dependency `CategoryTheory.CondensedBar.condensed_bar_scalar_resolution_comparison`
remains sorry in its own unchanged module, node
`lem-sfb-condensed-bar-scalar-resolution-comparison`; this is a proof from an already
stated dependency, not a new decomposition. No other module is delivered.

## No longer needed

Removed these direct private proof imports:

- `Sheaf.CategoryTheory.CondensedProductActionInflation`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality`
- `WeilConjectures.CategoryTheory.DoubleComplexTotal`
- `WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison`
- `WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`
- `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`
- `Mathlib.Algebra.Homology.ModelCategory.Injective`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`

These old direct proof dependencies are subsumed by the existing scalar-resolution
assertion and are removed from this node's proof_deps:

- `lem-sfb-condensed-product-action-inflation`
- `lem-sp-grothendieck-enough-injectives`
- `lem-pc-sites-modules-j-shriek-flat`
- `lem-sfb-condensed-split-coset-induction`
- `lem-sp-right-adjoint-preserves-injectives`
- `lem-sfb-condensed-injective-bar-rows`
- `lem-sfb-condensed-bar-total-augmentation`
- `lem-sp-derived-injective-resolution-naturality`
- `lem-sfb-condensed-bar-total-naturality`

Removed all ten old top-level tool_uses approvals, now unused directly:
`lem-pc-sites-modules-j-shriek-flat`, `lem-pc-sheaf-modules-tensor-closed`,
`lem-sp-derived-injective-resolution-naturality`,
`lem-sc-first-quadrant-total-column-comparison`,
`lem-weil-pbc-injective-resolution-lift-exists`, `lem-sfb-dc-hom-scalar-adjunction`,
`lem-weil-pbc-lift-along-injective-quasi-iso`,
`lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`,
`lem-sfb-condensed-split-coset-induction`, and
`lem-sp-right-adjoint-preserves-injectives`.

This removes direct dependencies only: several modules remain reachable through
public statement dependencies or the scalar-resolution module's own argument. No
whole module is asserted globally pruned, and no upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The six-step DAG plan and the preserved nine-step declaration docstring predate the
current scalar-resolution signature, which already includes the complete normalized
bar models. Reconstructing them again is unnecessary: the existing dependency is
strictly stronger than the requested assertion. Its free-parameter properties,
derived scalar-Hom comparisons, chain squares and independence clauses are additional
data discarded by the projection. No mathematical discrepancy was needed to obtain
this route; the unit's own statement and realized steps are untouched.

Searches run through msearch.py: LeanFinder on derived internal invariants via total
bar complexes returned ordinary `Rep.barComplex`, `Rep.barResolution`, group homology
and cohomology results, which do not supply internal condensed-ring coefficients;
Loogle on `"Condensed", "derived"` and grep on condensed bar/invariants returned no
matches. Source searches found `ScalarResolutionAssertion` as the applicable existing
result. The import-direction check allows the new private dependency. A transitive DAG check
also confirms the scalar-resolution dependency does not reach the item, so the proof
introduces no dependency cycle.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
