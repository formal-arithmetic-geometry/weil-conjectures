## What changed

Proved `AlgebraicGeometry.ProEtale.unboundedSiteComparison` with its exact original
signature, universes and public imports. Use the existing
`finiteClassicalUnboundedComparison` for classicality of derived inverse image and
invertibility of the canonical derived counit. Exactness and full faithfulness of
underived inverse image imply reflection of derived isomorphisms through the natural
cohomology comparison. The left triangle identity then makes the derived unit invertible.
Compose its fully faithful left adjoint with the coefficient realization equivalence and
transport along the canonical derived-composition isomorphism. The same adjunction and
realization equivalence preserve every requested discrete colimit, in any index universe.
Updated the item's DAG proof and dependencies to this shorter route.

Retained and checked two proof completions from the earlier sandbox:
`AlgebraicGeometry.ProEtale.finiteCoefficientRealization_full_faithful_essSurj` in
`Sheaf.Paper.RefinementCoefficientRealization`, using the ring-general realization
equivalence; and `AlgebraicGeometry.ProEtale.siteComparison_boundedBelow` in
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`, using the required finite-level comparison
unit and injective acyclicity, followed by the derived-unit criterion, then exact realization. Their signatures,
visibility, definitions and public imports are unchanged. Both modules are unclaimed;
no consumer needs adaptation. The current site-comparison node already records the
underived-unit and injective-acyclicity route, so no change to that node is needed.

The unchanged source of `Sheaf.AlgebraicGeometry.FiniteClassicalUnboundedComparison`
is included in the sandbox to compile its already-existing declaration on the server,
where its published artifact was absent. Its contents are byte-identical to the repository;
this is no new statement, definition or hole. No launcher script was modified.

## Proved and sorry left

Assigned item: proved 1 of 1 original holes,
`AlgebraicGeometry.ProEtale.unboundedSiteComparison`; zero holes remain in that module.
Also closed `AlgebraicGeometry.ProEtale.finiteCoefficientRealization_full_faithful_essSurj`
and `AlgebraicGeometry.ProEtale.siteComparison_boundedBelow`; zero holes remain in either
changed dependency module. Three existing holes closed across the delivery, zero added,
zero split off. This proves the item from existing stated dependencies, as stage 3 intends;
it does not claim those dependencies have no transitive holes.

The byte-identical compilation copy retains the one existing hole
`AlgebraicGeometry.ProEtale.finiteClassicalUnboundedComparison`, node
`lem-sfb-finite-classical-unbounded-comparison`. Its geometric fixed-degree truncation
and classical essential-image argument remains the existing downstream work item.
It is not a new hole of this delivery. The earlier unlanded affine-section split is not
delivered; its source and node draft are retained under scratchpad for work history.

On resumption, `lcompile.py --all` compiled all four sandbox modules successfully
against the current published build (1.4, 0.1, 1.1 and 1.3 seconds). The bounded-below
proof explicitly uses `siteComparison_finiteLevel` for its unit and injective acyclicity,
preserving the required unit route. The required delivery dry run additionally checks
signatures, axioms and preflight before the final push.

## No longer needed

Removed direct proof imports from the assigned module:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison`
- `Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized`
- `Sheaf.CategoryTheory.DerivedCategory.FiniteCDDerivedUpperBound`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.Algebra.Homology.HomologicalComplexLimits`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`
- `Sheaf.AlgebraicGeometry.EtaleModuleAffineBound`
- `Sheaf.AlgebraicGeometry.InjectiveComplexSliceSectionModel`
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
- `Sheaf.SixFunctors.ClassicalModuleAffineEvaluationBound`
- `Sheaf.SixFunctors.UnboundedClassicalTruncation`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`

Removed direct proof imports from `ProEtaleSiteComparisonDerived`:

- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`

The main proof instead imports `FiniteClassicalUnboundedComparison` and the source-library
comparison full-faithfulness and exact-derived-functor APIs. The new affine-section
module and new node from the retained attempt are unnecessary and are not delivered.
No existing repository module is withdrawn.

The following original direct proof dependencies are no longer direct dependencies of
this proof (geometric work that the existing classical-counit theorem still uses stays
reachable there and is not claimed as globally pruned):

- `det-pe-classical-sheaves-modules`
- `prop-pur-kinjective-resolutions-exist`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-termwise-adjunction-homotopy`
- `lem-pc-right-derived-functor-triangulated`
- `lem-pur-kinjective-restrict-localized`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-weil-pbc-comparison-pullback`
- `lem-sfb-etale-module-affine-bound`
- `lem-sp-grothendieck-enough-injectives`
- `lem-pe-injective-complex-slice-section-model`
- `lem-sfb-classical-module-affine-evaluation-bound`
- `det-pe-unbounded-classical-truncation`
- `def-sbc-standard-tstructure-derived-category`
- `lem-sf-finite-cd-derived-upper-bound`
- `lem-sf-derived-homology-long-exact`
- `lem-weil-pbc-comparison-global-cohomology`
- `lem-weil-pbc-site-r-module-presheaf-sheafification-exact`
- `lem-weil-pbc-affine-etale-essentially-small-cover`
- `lem-weil-pbc-ring-sheaves-grothendieck`
- `lem-kun-grothendieck-derived-coproducts`

In particular a separate derived-coproduct existence theorem is unnecessary: the
statement asks for preservation, supplied by the actual left adjunction. The node's
obsolete tool_uses entries were removed without reordering those retained. Global
pruning and import-closure hole counts remain the ledger's calculation.

## Where the brief, the DAG or earlier work was wrong

The interrupted sandbox main proof had two local `sorry`s while its report described
an older complete proof from a new affine-section lemma. The required initial dry run
correctly rejected that mismatch. The existing theorem
`finiteClassicalUnboundedComparison` now supplies exactly those two missing facts,
including the positive nilpotence exponent obtained from n by n+1. Thus no new local
comparison split is needed. The source declaration exists but initially had no published
server artifact; an unchanged sandbox compilation copy resolves that validation issue.
The import-direction check confirms that this dependency does not reach the assigned
module. The finite-level comparison module is retained and its theorem supplies both inputs
to the bounded-below derived-unit criterion, preserving that unit route. The main
module still sees the geometric comparison declarations through the unchanged public
import of ProEtaleFiniteModules, which publicly imports ProEtaleSiteComparison. The
classical-counit node retains the geometric bounded-below and finite-CD truncation argument.

The two retained dependency proofs change no existing interface or target. Their change
records are `coord/changes/K7-finiteCoefficientRealization_full_faithful_essSurj.md` and
`coord/changes/K7-siteComparison_boundedBelow.md`.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
