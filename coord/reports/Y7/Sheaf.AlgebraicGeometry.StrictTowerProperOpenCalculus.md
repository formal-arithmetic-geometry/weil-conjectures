## What changed

Changed only `lean/Sheaf/AlgebraicGeometry/StrictTowerProperOpenCalculus.lean`.

Proved `AlgebraicGeometry.ProEtale.StrictTower.gamma_isIso` from the existing
`gamma_evaluation`: each evaluated arrow is isomorphic to the image of the specified
finite etale comparison; cancellation makes it invertible. The exact-evaluation homology
comparison identifies every component of each tower-cohomology arrow with an invertible
map. Pointwise invertibility of natural transformations and `DerivedCategory.isIso_iff`
then prove invertibility in the unbounded derived category. No uniform lower bound is used.

Proved all three clauses of
`AlgebraicGeometry.ProEtale.StrictTower.normalizedProperOpenCalculus` from the existing
`alpha_vertical`, `alpha_horizontal`, and `alpha_baseChange` statements. These are converted
into equalities of pasted `TwoSquare`s; the Mathlib mate-pasting and conjugation lemmas give
the prescribed gamma equations with precisely `rComp`, `jComp`, and `exchange`.
Equality is established on derived tower transformations, without any evaluation-faithfulness
assumption. The proof follows steps 16--18 of the existing node, so no DAG route changes.

Added two proof-only imports for the exact-functor homology comparison and the additional
mate-whiskering identities. Kept every existing declaration signature, definition,
public import, and docstring unchanged. Both the transparency elaboration option and the unused-variable linter are scoped only to
`normalizedProperOpenCalculus`, whose preserved statement includes the two cartesian
hypotheses `sp` and `sr` that are absent from its conclusion.

Validation: the final module, including import pruning, compiled cleanly against the current sources through
`lcompile.py` in 22.1 seconds on resumption (2026-10-19). Every source line is at most 100 characters.

## Proved and sorry left

Closed 2 of the original 12 holes:

- `AlgebraicGeometry.ProEtale.StrictTower.gamma_isIso`.
- `AlgebraicGeometry.ProEtale.StrictTower.normalizedProperOpenCalculus`.

Added 0 holes and 0 split-offs. The 10 remaining holes are unchanged named theorem proofs,
all attached to node `lem-cbc-strict-tower-proper-open-calculus`:

- `AlgebraicGeometry.ProEtale.StrictTower.pi_components`.
- `AlgebraicGeometry.ProEtale.StrictTower.alpha_cartesian`.
- `AlgebraicGeometry.ProEtale.StrictTower.beta_id`.
- `AlgebraicGeometry.ProEtale.StrictTower.beta_comp`.
- `AlgebraicGeometry.ProEtale.StrictTower.beta_open_comp`.
- `AlgebraicGeometry.ProEtale.StrictTower.alpha_vertical`.
- `AlgebraicGeometry.ProEtale.StrictTower.alpha_horizontal`.
- `AlgebraicGeometry.ProEtale.StrictTower.alpha_baseChange`.
- `AlgebraicGeometry.ProEtale.StrictTower.gamma_evaluation`.
- `AlgebraicGeometry.ProEtale.StrictTower.gamma_identities`.

The two completed proofs intentionally use the existing named statements that remain
sorried, as required by stage 3. This is a net reduction of two holes, not a decomposition.

## No longer needed

Removed these 37 unused direct proof imports:

- `Sheaf.CategoryTheory.DiagramSiteRealization`.
- `Mathlib.Algebra.Category.Grp.FilteredColimits`.
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`.
- `Mathlib.CategoryTheory.Sites.Limits`.
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.Algebra.Homology.TowerEvaluationKInjective`.
- `Mathlib.Algebra.Homology.Functor`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`.
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`.
- `Sheaf.Paper.LocalizeRingedSiteMorphism`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`.
- `Sheaf.AlgebraicGeometry.DerivedOpenRestriction`.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.AlgebraicGeometry.ProperSupportSheafComposition`.
- `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`.
- `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`.
- `Sheaf.CategoryTheory.Adjunction.CoefficientExchange`.
- `Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`.
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`.
- `WeilConjectures.Algebra.Homology.TowerEvaluationKInjective`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.

These are redundant direct imports for the written proofs. No DAG node or whole module is
claimed pruned from the targets' import closure: the remaining holes still have their
existing proof plans, and supporting operations already import their own implementation
requirements. In particular the K-injective/scalar/site-comparison arguments are encapsulated
by `gamma_evaluation` rather than repeated in `gamma_isIso`.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction or signature repair was needed. The declared alpha equations
are sufficient to prove the complete gamma coherence package by mate pasting. Several
original proof imports describe construction work already encapsulated by dependencies and
were unnecessary in this module's completed proofs. The remaining normalization proofs
also need coherence of the particular section-normalized compositors; generic existence of
pullback-composition isomorphisms alone does not identify these particular arrows.

A scratch calculation verified the image-component equation of `pi_components` using
only the two adjunctions, the invertible open unit, and `openToR_isIso`. The complement-zero
component remains the geometric part; no helper or relocated hole from this calculation
is included in the delivery.

The retained sandbox was checked against the current module. Only the two proof bodies,
their proof imports, and declaration-scoped elaboration/linter options differ. No added
helper theorem, definition, signature change, or new node is included.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
