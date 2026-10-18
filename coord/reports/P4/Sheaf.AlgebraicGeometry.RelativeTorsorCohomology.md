## What changed

Changed `lean/Sheaf/AlgebraicGeometry/RelativeTorsorCohomology.lean` and the proof fields of
`dag/nodes/sec-smooth-purity/lem-amb-relative-torsor-cohomology.json`.
All existing signatures, public imports and public definitions are unchanged.

Restriction and transfer squares follow sectionwise naturality. Comparison existence and
uniqueness use that the direct image, as right adjoint to exact inverse image, preserves
injectives. The degreewise recursion constructs a comparison and a homotopy for comparisons
with equal augmentation. Evaluation, extension by zero and the signed cone preserve that
homotopy. The cone calculation uses Mathlib's cochain differential and proves the required
negative sign rather than assuming it.

Split section rows remain split after extension by zero. In each degree the cone row is the
biproduct of two such rows, so it is short exact. This gives both relative and absolute short
exact sequences. The existing source horseshoe theorem supplies the resolutions for the
coefficient sequence. The three connecting-map compatibilities are applications of
`HomologicalComplex.HomologySequence.δ_naturality` to explicit short-complex morphisms.

Added the private proof imports `Mathlib.CategoryTheory.Preadditive.Comma` and
`Mathlib.Algebra.Homology.HomologySequenceLemmas`. Retained the direct source import
`WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions`. Removed the other proof imports
listed below. The module compiles with these three private imports.

## Proved and sorry left

Closed 11 of the 12 original holes, with no holes added and no splits:

- `AlgebraicGeometry.Etale.relativeSectionMap_square`
- `AlgebraicGeometry.Etale.relativeTransfer_square`
- `AlgebraicGeometry.Etale.relative_comparison_exists`
- `AlgebraicGeometry.Etale.relativeTransfer_independent`
- `AlgebraicGeometry.Etale.relativeSectionMap_comp_zero`
- `AlgebraicGeometry.Etale.relativeShortComplex_shortExact`
- `AlgebraicGeometry.Etale.relativeAbsoluteShortComplex_shortExact`
- `AlgebraicGeometry.Etale.relativeConnecting_forget`
- `AlgebraicGeometry.Etale.relativeConnecting_pullback_naturality`
- `AlgebraicGeometry.Etale.relative_coefficient_sequence`
- `AlgebraicGeometry.Etale.relativeConnecting_coefficient_naturality`

The sole remaining `sorry` is
`AlgebraicGeometry.Etale.relative_torsor_cohomology`, attached to
`lem-amb-relative-torsor-cohomology`. Its original complete proof plan remains in its
docstring and DAG node. The missing work is the pointed lifting-torsor/cocycle bijection,
its identification with degree-one homology of the shifted cone, normalization against
`ResolutionSectionCanonicalComparison`, and naturality on representatives. The eleven
supporting statements above are fully proved, not moved to renamed obligations.

Validation: the complete item compiles without warnings through `lcompile.py` (21.1 seconds
of server compilation for the first clean version). Individual `#print axioms` checks for all
eleven closed declarations report only `propext`, `Classical.choice` and `Quot.sound`; none
uses an unproved theorem. No public definition body or existing declaration signature changed.
The required `deliver3.py --no-push` run passed compilation and preflight, with review class
`CODEX` because the delivery updates a node's proof fields.

## No longer needed

Removed these 21 private imports; none is needed as a direct import for the delivered code:

- `WeilConjectures.CategoryTheory.Sites.Torsor`
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.CategoryTheory.Sites.Sheaf`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`
- `Sheaf.CategoryTheory.Sites.EtaleContractedProductExists`
- `Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality`
- `WeilConjectures.AlgebraicGeometry.CohomologyPullbackDerivedUnit`
- `WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.CategoryTheory.Abelian.HorseshoeMorphismLift`
- `Sheaf.CategoryTheory.Abelian.HorseshoeResolutions`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.CohomologyPullbackCanonicalArrows`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.CategoryTheory.Abelian.SplitSESBoundaryComparison`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`

Removed the direct proof dependency `lem-weil-pbc-kinjective-hom-derived`: comparison
uniqueness is proved by an explicit null-homotopy recursion. Its obsolete `tool_uses` entry
is also removed. No whole DAG node or module is withdrawn. This partial delivery does not
claim that the remaining classification theorem can dispense with its planned torsor
construction or its semantic comparisons with derived cohomology. The node still
records that remaining plan, with the comparison and concrete-complex proofs updated. Those supporting proofs require
neither a new fibre-descent theorem nor new split-boundary comparison obligations.

## Where the brief, the DAG or earlier work was wrong

No statement was found false, and no definition or interface was changed. The concrete
connecting-map statements admit a direct proof from short-exact-sequence naturality; the
additional abstract derived-category descent route is unnecessary for these statements.
Comparison existence and independence admit a direct recursion into injective direct-image
terms, without choosing pulled-back resolutions or using a Hom-to-derived bijection.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
