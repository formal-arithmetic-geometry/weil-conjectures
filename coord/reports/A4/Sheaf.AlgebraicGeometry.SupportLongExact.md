## What changed

Proved `AlgebraicGeometry.exists_support_longExact` with its existing statement unchanged.
The construction works for all coefficients first and is restricted to torsion coefficients
for the etale factor. The pro-etale factor is constructed directly in the stated module
category. Added the fully proved generic normalized-boundary construction in
`Sheaf.CategoryTheory.DerivedInjectiveBoundary`; it constructs the boundary on every
injective representative and transports exactness through the canonical derived units.
The unique pair support map is the kernel lift, and its boundary square follows from
Mathlib homology-sequence naturality. Module-injective restriction surjectivity is proved
locally using free lifted representable module presheaves and the sheafification adjunction.
Existing public statements, definitions, and public imports are unchanged.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.exists_support_longExact`
(node `thm-pur-with-support-exactness`). Added zero holes. No `sorry` remains in either
delivered Lean module. The new theorem
`CategoryTheory.Functor.exists_injectiveBoundary` and all its supporting results are proved.
This is a proof, not a decomposition into unproved intermediate statements.
The proof uses the existing additive instance of supported sections; its upstream proof
status is unchanged.

## No longer needed

The following proof imports were removed:

- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `Mathlib.Algebra.Homology.HomologySequence`
- `Mathlib.Algebra.Homology.HomologySequenceLemmas`
- `Mathlib.CategoryTheory.Abelian.RightDerived`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen`
- `Sheaf.AlgebraicGeometry.InjectiveComplexSliceSectionModel`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
- `Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget`
- `Sheaf.CategoryTheory.ModuleRestrictionKernelComparison`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization`
- `Sheaf.Paper.SiteRestrictionInjectives`
- `Sheaf.Paper.SupportPairChainCoherence`
- `Sheaf.Paper.SupportPairComposition`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`
- `WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf`
- `WeilConjectures.CategoryTheory.SiteMorphismComposition`

The following formerly declared proof dependencies are removed from the item's direct
proof-dependency list:

- `def-sp-left-exact-additive`
- `def-weil-pbc-direct-image`
- `def-weil-pbc-inverse-image`
- `def-weil-pbc-proetale-modules`
- `def-weil-pbc-sites-and-cohomology`
- `def-weil-proetale-inverse-image`
- `lem-pe-constant-left-module-inverse-image`
- `lem-pe-injective-complex-slice-section-model`
- `lem-pe-left-module-derived-evaluation-forget`
- `lem-pur-module-restriction-kernel-comparison`
- `lem-pur-support-pair-chain-coherence`
- `lem-pur-support-pair-composition`
- `lem-weil-pbc-cohomology-over-object-localization`
- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-etale-cohomology-over-open`
- `lem-weil-pbc-inverse-image-composition`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-right-derived-plus-injective`
- `lem-weil-pbc-site-morphism-composition`
- `lem-weil-pbc-site-pullback-abelian-exact`
- `lem-weil-pbc-site-restriction-injectives`
- `lem-weil-proetale-weakly-etale-localization`
- `prop-weil-pbc-inverse-image-exact`
- `prop-weil-pbc-proetale-constant-ring-map`

The derived-category/injective-representative and natural-transformation leaves remain
needed transitively in the new proved generic helper; they are not claimed as pruned from
the full import closure. Some removed direct Mathlib imports are likewise supplied through
that helper. The list records direct-import and direct-node pruning, not global deletion.

The generic construction operates on actual section complexes, exactly as the Lean
statement defines its functors. It therefore needs no additional identification with a
localized-site cohomology model. Its pair clause quantifies every adjoint chain map and
uses the unique kernel lift directly; no separate inverse-image composition or chain
coherence theorem is required. The pro-etale construction stays in module coefficients
throughout, so scalar forgetting, constant-ring comparisons, twists, and comparison with
the etale site are unnecessary. The following unused maintainer `tool_uses` entries are withdrawn from the node copy:

- `lem-weil-pbc-cohomology-over-object-localization`
- `lem-weil-pbc-etale-cohomology-over-open`
- `lem-weil-pbc-proetale-restriction-injectives`
- `lem-weil-pbc-site-pullback-abelian-exact`
- `lem-weil-pbc-site-restriction-injectives`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-weil-pbc-site-morphism-composition`
- `prop-weil-pbc-inverse-image-exact`
- `lem-weil-pbc-inverse-image-composition`
- `lem-pe-injective-complex-slice-section-model`
- `lem-pe-left-module-derived-evaluation-forget`
- `lem-pe-constant-left-module-inverse-image`
- `def-weil-pbc-proetale-modules`
- `prop-weil-pbc-proetale-constant-ring-map`
- `def-coefficient-twists-detailed`

These withdrawals concern proof use; the fixed-unit import is retained. The fixed-unit import `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` and its
`def-coefficient-twists-detailed` dependency are retained, as required by preflight.
No unit statement or realized step is bypassed, and no module is
withdrawn: other parents may still need these dependencies.

## Where the brief, the DAG or earlier work was wrong

The inherited sandbox was unfinished and did not compile. Its main remaining issues were
universe inference for the two derived categories, a restriction-square elaboration issue,
and unfolding the normalization across a full-subcategory inclusion. These have been
repaired without changing any existing signature. The retained final assembly also
requested the sheaf derived category in universe `u + 2`; it now uses the available
Grothendieck derived-category instance in universe `u + 1`, with explicit universe
arguments on both boundary choices and their specifications. Explicit local coefficient
derived-category instances select the same Grothendieck model as the unchanged
statement, rather than the larger standard model introduced by a proof import. The resumed dry run identified a
required change record for added module-local universe/variable commands and a
fixed-unit import that must stay; both diagnostics are addressed in this delivery.
Explicit continuity arguments account
for the topology alias used in the etale instance. The longer original plan contains
localization and coefficient-comparison clauses not present in the exact Lean proposition;
the direct two-site construction proves the proposition without them. The existing source
correction is retained: restriction need only be surjective on injective terms, and the
pro-etale argument must allow coefficients that do not descend to the etale site.

## New nodes

`lem-pur-derived-injective-boundary`, in
`dag/nodes/sec-smooth-purity/lem-pur-derived-injective-boundary.json`, records the fully proved
normalized connecting transformations for a sequence of additive functors exact on
injectives. It is a separate generic homological result from the coefficient-naturality
part of the source argument; its hypotheses do not mention sites, schemes, support,
torsion, or pairs. Identity/composition and zero/degenerate cases require no additional
hypotheses: the natural transformation and the kernel universal property cover them.
The change record is `coord/changes/A4-support-long-exact-proof-context.md`; it records
the additional private proof context and new generic API. Existing definitions and
statements do not change.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
