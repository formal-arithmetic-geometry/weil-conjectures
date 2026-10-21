## What changed

Restored the assigned module from its recorded quarantine source. Preserved the full
signature and all four public imports of
`AlgebraicGeometry.Scheme.integralConstructible_boundedBelow_compactness`.
Its proof now composes internal-Hom coproduct preservation, a uniform internal-Hom
lower bound, and integral derived-global-sections coproduct preservation. The final
universal-property argument applies to the original supplied cofans and coprojections.
The unit route and coefficient constructions are unchanged.

Added and proved two auxiliary results:

- `AlgebraicGeometry.Scheme.proEtale_internalHom_isGE`: use representatives with
  the original bounds and a same-bound injective resolution; every Hom-product factor
  below N-b vanishes. This works for any commutative coefficient ring sheaf.
- `AlgebraicGeometry.Scheme.proEtale_derivedGlobalSections_boundedBelow_preservesColimit`:
  arbitrary ring-sheaf coefficients and any scalar homomorphism A→Γ(T,R), without a
  rational-algebra assumption. Classical derived evaluation preserves coproducts;
  sums of uniformly bounded-below injective representatives have sections-acyclic
  terms, so the acyclic comparison proves the unbounded-derived assertion on this family.

The latter proof reuses the proved, coefficient-general private helpers
`qcqs_evaluation_preservesCoproducts`, `rightDerivedExactCompIso`, `unit_of_acyclic`
and `uniformCoproduct` through `import all`. It does not apply the public rational-only
direct-image theorems to integral coefficients. Its generality is needed on slices
and for inverse-image coefficients in the remaining stratification argument.

The remaining independent result is sheaf-valued internal-Hom continuity for an
arbitrary bounded-above stratified perfect source over an arbitrary adic datum.
It contains the local/open/closed devissage from BS 6.3.14(2)–(4) and 6.8.12.
It does not assume the original global comparison and does not involve finite
extensions, finite Krull dimension, or the original constructible-complete predicate.
The root proof combines it with the two proved results above and the existing
stratified-perfect characterization.

Validation: all four sandbox modules compile in import order through lcompile.py.
The main statement is unchanged, the original empty-family comparison is retained,
and the auxiliary arguments also cover zero objects and the empty scheme.
No upstream declaration, existing definition, or other group's module is changed.

## Proved and sorry left

Original hole discharged, as a decomposition:
`AlgebraicGeometry.Scheme.integralConstructible_boundedBelow_compactness`
(`lem-weil-pbc-integral-constructible-bounded-below-compactness`). Its body is complete.

Two newly proved theorems, with zero holes in their modules:
`AlgebraicGeometry.Scheme.proEtale_internalHom_isGE`
(`lem-weil-pbc-proetale-internal-hom-lower-bound`) and
`AlgebraicGeometry.Scheme.proEtale_derivedGlobalSections_boundedBelow_preservesColimit`
(`lem-weil-pbc-adic-derived-sections-bounded-below-coproducts`).

One hole added and remaining:
`AlgebraicGeometry.Scheme.integralStratifiedPerfect_internalHom_preservesColimit`
(`lem-weil-pbc-stratified-perfect-internal-hom-coproducts`), in
`Sheaf.Paper.StratifiedPerfectInternalHomCoproducts`.
Its proof is exactly `by sorry`, with source and the full seven-step argument in its
docstring and a matching node. No other sorry is introduced. This is one original
hole replaced by one strictly internal part of its argument, hence a decomposition
with net zero holes closed, not a claim of a complete axiom-free proof.
The already-stated characterization and helper dependencies retain their existing status.

## No longer needed

Removed these private imports from the assigned module:

- `Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck`
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.Algebra.Homology.HomologicalComplexLimits`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`
- `Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover`
- `Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits`
- `WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `WeilConjectures.Algebra.Homology.RhomGlobalSections`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`
- `Sheaf.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`
- `WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`
- `WeilConjectures.Topology.Stratification`
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`
- `Sheaf.AlgebraicGeometry.ProEtaleClosedLocalization`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`

The main node's direct proof dependencies now consist of the characterization,
the three auxiliary nodes, the global-Hom definition, and the colimit universal property.
The local, geometric, and open/closed dependencies remain attached to the internal
continuity node: removing their imports here does not withdraw their mathematics.
The hypercover dependencies are reached through the existing general evaluation helpers.

`lem-weil-pbc-small-module-diagrams-grothendieck` is unnecessary as a separate input:
we use the already proved independent-universe module-category Grothendieck theorem.
`lem-sc-bounded-below-injective-resolution` is also unnecessary: Mathlib supplies
same-bound injective resolutions directly, via the existing
`lem-weil-pbc-dplus-injective-representative` infrastructure. Its obsolete top-level
`tool_uses` approval was removed from the parent node; other approvals retain their order.
No module is withdrawn and no source-library declaration is removed. Whole-closure
module pruning is left to the ledger; no modules are claimed pruned by this packet.

## Where the brief, the DAG or earlier work was wrong

The item was quarantined rather than withdrawn; its rework row identifies the archive,
and that archive is restored, not deleted or replaced by an empty module.
There is no current item-specific return beyond the historical sync notice.

The original lower-bound plan used slice cohomology and t-structure orthogonality;
its statement follows more directly by choosing a bounded-above source and a
same-bound bounded-below injective target, and testing the Hom-complex product factors.
This avoids the same-universe limitation of several old ringed-site APIs.

The existing public pro-etale coproduct theorems require rational coefficients.
Their private classical-evaluation and bounded-below acyclic-comparison helpers
are genuinely coefficient-general; the new derived-global-sections theorem uses those
helpers with their actual hypotheses. It retains the integral scalar action.

The nearby constructible-source continuity statements concern condensed module
objects and fixed coefficient realizations. They do not directly accept the recorded
completed ring sheaf or arbitrary inverse-image coefficients. No identification of
these constructions is silently asserted. The remaining internal continuity lemma
records exactly the local/stratified part still requiring formalization.

## New nodes

`lem-weil-pbc-proetale-internal-hom-lower-bound` is the proved uniform amplitude
calculation, with its independent-universe ring-sheaf statement and same-bound
injective-resolution proof.

`lem-weil-pbc-adic-derived-sections-bounded-below-coproducts` is the proved
coefficient-general derived-sections continuity statement. Its proof explicitly records
the private helper signatures used from the two existing rational direct-image modules.

`lem-weil-pbc-stratified-perfect-internal-hom-coproducts` is the remaining local
finite-stratification devissage, before global sections. It depends on the two proved
nodes and the original restriction, geometry, and open/closed nodes. Its statement
is strictly internal and coefficient-general; the parent supplies constructible
characterization, the bound, global sections, and the actual comparison map.

All three nodes are in `sec-proper-base-change` and unit `sk-thm-properbasechange`,
with the original finite-extension blueprint ancestry. Each has three logged kinds
of Mathlib search and its verbatim Lean signature. No change record is needed:
no existing declaration's signature, visibility, or definition is changed.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
