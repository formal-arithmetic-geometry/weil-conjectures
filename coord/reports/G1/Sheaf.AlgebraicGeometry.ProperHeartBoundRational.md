## What changed

Proved the two existing declarations in `Sheaf.AlgebraicGeometry.ProperHeartBoundRational` with their signatures and public imports unchanged. Added four proved private helpers for empty geometric fibres, zero modules on the empty scheme, localization preserving a vanishing degree, and algebraic-closure scalar extension preserving a vanishing degree.

For finite rational coefficients, compare constructibility predicates, construct integral models on the strata and glue an ordinary constructible integral model. Apply `integralProperConstructibleHeartBound`, then the canonical localization telescope and exact faithful coefficient restriction. Negative dimension bounds are treated directly by the empty geometric fibres argument. For algebraic-closure coefficients, descend the degree-zero complex to a finite field, take degree-zero cohomology, and apply the rational result plus the ordinary scalar-basis copower decomposition. Only coproducts with common lower bound zero are used, through `condensed_boundedBelow_preservesCoproduct`; no ambient unbounded coproduct-preservation assumption is introduced.

Updated `det-proper-heart-bound-rational` to record this argument. The existing integral estimate supplies the completeness, classical torsion bound, and Milnor extra degree of the unit's lattice route. The stratum-model/gluing theorems implement its constructible reduction. All results used are existing declarations; no statement, definition, upstream source module, consumer, or unit record is changed. The new imports are private proof imports. Local irreducibility attributes keep the tensor construction and comparison functors abstract during elaboration; no underlying definition changes.

## Proved and sorry left

Closed 2 existing holes:

- `AlgebraicGeometry.ProEtale.isZero_higherDirectImage_rational_of_isProper` (`det-proper-heart-bound-rational`).
- `AlgebraicGeometry.ProEtale.isZero_higherDirectImage_padicAlgCl_of_isProper` (the same node).

Added 0 holes and split off 0 statements. There are no `sorry`s left in the delivered Lean file. This is a proof from existing library declarations; it does not claim that all their transitive proof obligations have been discharged.

## No longer needed

The direct weakly-contractible section calculation and separate lattice/reduction proof are replaced by the already available integral constructible estimate and ordinary integral models. The following private imports are removed (the repeated finite-coefficient import is removed in both positions):

- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`.
- `Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsExact`.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic`.
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`.
- `Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.CategoryTheory.KInjectiveComputes`.
- `Sheaf.AlgebraicGeometry.ProEtale.SectionsConservative`.
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`.
- `Sheaf.Paper.ModuleObjects`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `Sheaf.AlgebraicGeometry.ProperHeartContinuityDirectImage`.
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`.
- `WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`.
- `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`.
- `Mathlib.CategoryTheory.Monoidal.Mod`.
- `Sheaf.Paper.CompletedCondensedCoefficients`.
- `Sheaf.Paper.CartesianCoefficientsFiniteFree`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`.
- `Sheaf.Paper.ProperHeartBoundLattice`.
- `Sheaf.Paper.ProperHeartBoundReduction`.

The following former direct proof dependencies are no longer needed by this proof. This is a change to this item's dependency route, not a request to delete their declarations or to withdraw any module still used elsewhere:

- `det-proper-heart-bound-reduction`.
- `lem-pc-field-extension-surjective`.
- `lem-weil-pbc-surjective-base-change`.
- `sk-def-sfb-module-derived-pushpull`.
- `sk-def-sfb-module-pushforward-pullback`.
- `def-sfb-finite-lower-star`.
- `det-pe-wc-sections-exact`.
- `lem-weil-pbc-module-sheaves-colimits-forgetful`.
- `lem-sc-injective-module-abelian-acyclic-zariski`.
- `lemma-weil-pbc-leray-acyclicity`.
- `lem-weil-pbc-cohomology-over-object-localization`.
- `lem-weil-proetale-weakly-etale-localization`.
- `lem-sp-kinjective-computes`.
- `det-pe-sections-conservative`.
- `lem-pur-ringed-site-grothendieck-abelian`.
- `lem-sp-grothendieck-enough-injectives`.
- `sk-def-sfb-module-objects`.
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`.
- `det-proper-heart-bound-lattice`.
- `sk-def-sfb-dc-setting`.
- `def-weil-proper-morphism`.
- `def-weil-finite-type-morphism`.
- `def-weil-quasi-separated-morphism`.
- `def-weil-closed-immersion`.
- `det-proper-heart-continuity-direct-image`.
- `sk-prop-sfb-qlbar-colimit-x`.
- `sk-def-sfb-change-of-scalars`.
- `det-prop-sfb-cartesian-coefficients-finite-free`.

All old `tool_uses` approvals are removed as obsolete direct dependencies. Some of those results remain behind the existing integral estimate or continuity declarations; those transitive uses are retained. No upstream declaration is removed or replaced by a hole.

## Where the brief, the DAG or earlier work was wrong

The original planned proof asks this module to rebuild an integral sheaf cohomology calculation through the internal-module/ring-sheaf equivalence. The library now has `integralProperConstructibleHeartBound`, which already carries out the integral completeness/torsion/Milnor estimate for all constructible integral modules, and integral stratum-model/gluing declarations. Reusing them shortens the proof while keeping the same dimension estimate and coefficient interpretation. The old declaration docstrings remain the original proof plans; the updated node and the proof bodies record the actual implementation.

The other-unit existing tools used are integral stratum models and gluing, localization telescope continuity and flatness, and the algebraic-closure scalar basis; the integral estimate itself comes from the integral compactness unit. Each supplies an existing part of the same integral-lattice argument, rather than a replacement target or a new assumption. All fifteen replacement direct dependencies were checked through their statement and proof closures not to lead back to this item. Approval of any new cross-unit tool use remains with the maintainer.

Validation: the final cleaned module compiled without errors or warnings in 52.9 seconds using the required lcompile.py command. No heartbeat or compiler-time limit was raised. The two theorem signatures, all public imports and the existing docstrings were compared with the shared source and are identical; all Lean lines are at most 100 characters.

No mathematical statement was found false. The all-unbounded algebraic-closure push comparison would require extra continuity; the proof uses the common-lower-bound coproduct theorem instead. The negative-dimension case is retained, including empty sources and arbitrary integers q satisfying the original inequality.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
