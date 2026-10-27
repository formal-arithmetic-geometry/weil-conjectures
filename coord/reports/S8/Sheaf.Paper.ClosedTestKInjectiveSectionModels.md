## What changed

Filled the proof of `AlgebraicGeometry.ProEtale.ClosedTestKInjectiveSectionModels.closed_test_kinjective_section_models` in `lean/Sheaf/Paper/ClosedTestKInjectiveSectionModels.lean`, retaining its statement. The two pushforward complexes are K-injective by the exact inverse-image adjunctions. The three existential isomorphisms are the inverses of exactly the forward maps prescribed in the statement, so their normalization equations hold by reflexivity.

The public `ClosedTestUnitEvaluation` import supplies the concrete `fiberIso` used by definitions; the accompanying private `import all` and the private `WeaklyEtaleDerivedEvaluationRestriction` import reuse the already proved `internal_test_preservesHomology`, `internalSpecializationUnit_bijective`, `full_test_surjective` and `specializes_pullback` helpers of `ClosedTestUnitEvaluation`, and `module_weaklyEtale_preservesKInjective`, `localization_sections_iso` and `derived_pullback_iso` from `WeaklyEtaleDerivedEvaluationRestriction`. Their concrete maps are the actual units and diagonal restrictions in this module. A proved private helper applies these calculations to `localizationModel`. No new mathematical statement or hole is introduced.

Ordinary definitions for evaluation and the test objects, explicit return types, and explicit return types for `closedUnitComplex` bound repeated elaboration of nested coefficient and fibre-product data. The mathematical objects and maps are unchanged up to definitional equality. The proved `evaluationAdditive` instance records existing additivity. The change record is `coord/changes/S8-closed-test-section-model-elaboration.md`.

The node proof and proof dependencies now describe this assembly of existing concrete-map calculations. Searches used launcher LeanFinder, Loogle, LeanSearch and grep, together with direct searches in the source library and Mathlib.

## Proved and sorry left

The sole original hole is `AlgebraicGeometry.ProEtale.ClosedTestKInjectiveSectionModels.closed_test_kinjective_section_models`, node `lem-sfb-closed-test-kinjective-section-models`. Its complete proof is written. No `sorry` remains in the item module and none is added elsewhere. There are zero split-off statements. The final item and all ten unchanged downstream modules compiled successfully, with no warnings or errors, through the required launcher (`--all` consumer-validation result `e348296dd0d53e93e4205fcc`). The original `NatTrans.mapHomologicalComplex` construction of `closedUnitComplex` is retained, preserving existing downstream simplification proofs. There are no consumer edits. The sole original hole is closed and zero holes are added.

## No longer needed

The former indirect generic localization route is replaced by the existing concrete internal-module localization calculations in `WeaklyEtaleDerivedEvaluationRestriction`. Separate ring-level ind-etale stability is unnecessary: both test fibres are already objects of their full pro-etale sites. The abstract ringed-site localization/pullback theorem is unnecessary for the displayed final conjunction; its coefficient-compatible derived composition is already constructed by `derivedTestPullbackComposition`.

The obsolete direct dependencies are `lem-weil-pbc-ind-etale-stability`, `lem-sfb-unbounded-sections-localization`, and `lem-weil-pbc-localize-ringed-site-morphism`. Their top-level `tool_uses` approvals are removed, retaining the other approvals in their original order. No module is withdrawn and no claim is made that these dependencies are globally unused. Removed the private imports `Sheaf.RingTheory.IndEtaleStability`, `Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization` and `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`. Also removed redundant private imports `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`, `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`, `Sheaf.CategoryTheory.ExactDerivedComposition` and `Mathlib.CategoryTheory.Localization.Predicate`: the needed preserved-K-injective, exact-evaluation and derived-compositor APIs are already available through retained public imports. The three generic mathematical principles remain represented in the dependency record; their wrapper modules are not directly needed here.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically valid but used more general transport results than needed. Existing private helpers already implement internal-module localization and diagonal-unit normalization. No weak-contractibility hypothesis is needed on either source test fibre, and closed inverse image is never assumed to preserve K-injectives.

The normalization directions are preserved: `eLeft.inv`, `eUnit.inv` and `eRight.inv` are exactly the maps in the statement. The argument permits zero and unit ideals, empty tests, empty source schemes, zero complexes, and unbounded K-injective representatives. The original bounded-below hypothesis on K is retained. No target statement changes.

The retained attempt's disk-space failure is resolved: the required initial delivery check reached Lean. It exposed a kernel timeout in `closedUnit_app_isIso` caused by comparing separately elaborated copies of the closed-unit component. The final proof avoids that comparison by proving the evaluated unit and fibre restriction invertible separately. `closedUnit` retains its original definition. The change record now lists all ten downstream modules, including six newer consumers absent from the retained table. The original `closedUnitComplex` construction is restored to preserve downstream simplification proofs. No consumer source is changed.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
