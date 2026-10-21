## Worker report

The delivery states exactness and triangulated descent of the existing normalized
completed realization and constructs its localization, cohomology and shifted-module
natural isomorphisms. It introduces no second coefficient sheaf or realization functor.
The sole postponed theorem is
`AlgebraicGeometry.Scheme.integralConstantRealization_exact_derived`; its docstring
contains the five proof steps of the DAG node, with the dependencies for each step.
All comparison definitions contain actual compositions of existing canonical maps.

Hypotheses and objects, clause by clause:

- A scheme T is `(T : Scheme.{u})`, with its original small pro-etale site
  `T.ProEt` (objects in u+1, morphisms in u). No equality of these universes is imposed.
- The ring is `{A : Type (u + 1)} [CommRing A]`; the coefficient hypothesis is
  `(d : AdicCoefficientDatum A)`. The recorded structure includes Noetherianity,
  the ideal and its finite generation, additive torsion of A/I, perfect quotient
  modules and finiteness of all positive quotients. No additional assumptions occur.
- B_T is the existing `adicLisseCompletedRing T d.ideal`. A_T is the existing
  `pbcAdicCompletion T d`. The isomorphism gamma is `pbcCompletedComparison T d`,
  defined by `HasLimit.isoOfNatIso (pbcConstantSystemComparison T d)`; its level maps
  are exactly the sheafified constant-function maps `AdicCoefficients.constantComparison`.
- F_T is `integralConstantModule T d`, whose definition is
  `completedKoszulConstant T ... ⋙ pbcRestrict (pbcCompletedComparison T d).inv`.
  `completedKoszulConstant` is `adicLisseConstantModules T A ⋙
  completedConstantExtension T (adicDatumScalar T ...)`. Thus it is constant module
  sheafification, tensor extension to B_T and restriction along gamma inverse, as required.
- Additivity is `(integralConstantModule T d).Additive`; exactness is
  `PreservesFiniteLimits ... ∧ PreservesFiniteColimits ...`, the two middle conjuncts
  of the main theorem. Its helpers use the already published `integralConstantModule_exact`
  to construct the comparison data; there is no new exactness hypothesis.
- DF_T is the recorded `integralConstantDerived T d`, defined by the exact functor's
  `mapDerivedCategory` with the standard algebra-module derived localization. Its
  triangulated exactness is `(integralConstantDerived T d).IsTriangulated`.
  `integralConstantDerived_commShift` exposes its existing canonical shift structure;
  the instance merely unfolds the existing derived functor and infers that structure.
- The termwise localization comparison is `integralRealizationFactors T d`:
  `completedConstantQ (ModuleCat A) ⋙ integralConstantDerived T d ≅
  (integralConstantModule T d).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q`.
  Its construction is exactly `mapDerivedCategoryFactors`. The theorem also states
  `NatTrans.CommShift (integralRealizationFactors T d).hom ℤ`, fixing compatibility
  of this comparison with the localized identity-on-components shift structure.
- The first displayed comparison is `integralRealizationHomologyIso T d q`, of type
  `H^q ⋙ integralConstantModule T d ≅ integralConstantDerived T d ⋙ H^q`.
  It is the existing `mapDerivedCategoryHomologyFunctorIso q`, with the node's forward
  orientation F(H) to H(DF). Inspection of its full source shows that it is the
  localization lift of the inverse complex cohomology comparison followed by the
  inverse factorization comparison. The source normalization theorem is
  `mapDerivedCategoryHomologyFunctorIso_hom_app_Q`. The complex comparison is
  `mapHomologicalComplexHomologyIso`, induced by preservation of cycles and boundaries.
- The second displayed comparison is `integralRealizationShiftedModuleIso T d r`.
  Its source functor is `(singleFunctor A 0 ⋙ shiftFunctor _ r) ⋙ DF` and its target
  is `F ⋙ (singleFunctor (pbcModules ...) 0 ⋙ shiftFunctor _ r)`. It is the composition
  of the associator, `commShiftIso r`, the inverse associator,
  `mapDerivedCategorySingleFunctor 0` whiskered by the target shift, and the associator.
  Thus M[r] means the shift of the degree-zero complex, not the complex in degree r.
  The single comparison is induced by `singleMapHomologicalComplex` and the same
  localization factorization; its shifted component is the prescribed identity on F(M).
- Naturality in P and M is encoded by isomorphisms of FUNCTORS, rather than pointwise
  existence of unrelated isomorphisms. The binders `(q : ℤ)` and `(r : ℤ)` cover every
  degree and shift. The domain is the unbounded `DerivedCategory (ModuleCat A)` and
  M ranges over all of `ModuleCat A`, with no finiteness or boundedness predicates.

Dependency declarations used (including the public import closure):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Sheaf.Paper.AdicCoefficientDatum` and `Sheaf.Paper.CompletedAdicCoefficientDatum`:
  `AdicCoefficientDatum`, `completedReductionTower`, and the existing coefficient data.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.Paper.IntegralStratifiedPerfectModels`: `integralConstantModule`,
  `integralConstantModule_exact`, `integralConstantModule_additive`, `integralConstantDerived`.
- `Sheaf.Paper.BoundedConstructibleTower`: `pbcModules`, `pbcCompletedComparison`,
  `pbcLevelConstantComparison`, `pbcConstantSystemComparison`, `pbcRestrict`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, `DerivedCategory.homologyFunctorFactors`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, already used by the tensor extension.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, underlying `pbcRestrict`.
- The proof-only imports include all stated proof dependencies: `FiniteTypeConstantExact`,
  `SiteConstantModuleFunctorGeneral`, `CompletedConstantSheafReduction`,
  `ShortComplex.PreservesHomology`, `Localization.Predicate`. The exact derived
  factorization and homology interfaces come from Mathlib's `DerivedCategory.ExactFunctor`
  and `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.

Edge cases checked: empty schemes/sites; the zero module and zero complex; zero ring;
I = 0 or I = top whenever they satisfy the datum; q negative, zero and positive;
r negative, zero and positive; unbounded P and infinitely generated M. All expressions
remain defined and none of these cases is excluded by a binder or local model condition.
For shifts the potentially nonzero term is in degree -r, as in the source. The universe
choice is the recorded size convention, and retains the unequal pro-etale site universes.

Searches made before writing:

- `msearch.py ... leanfinder "Exact completed constant module realization preserves derived
  cohomology and shifted degree zero complexes"`: eight hits (Ext and group cohomology
  calculations), none states this completed coefficient realization result.
- `msearch.py ... loogle '"mapDerivedCategory", "homology"'`: zero hits.
- `msearch.py ... grep 'mapDerivedCategory.*(homology|Single)|integralConstant'`:
  ten hits, principally `mapDerivedCategorySingleFunctor` and its degree-zero
  normalization lemmas. These supply the canonical general interface, not the full node.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `integralConstant`,
  completed realization, and realization/homology found the recorded realization,
  its exactness theorem and applications of the general derived comparisons in
  `IntegralStratifiedPerfectCharacterization`. It found no declaration of this whole node.
- `rg` for the exact node id in `lean/WeilConjectures` returned no hit. Searches for
  all five proposed declaration names in Mathlib, WeilConjectures and Sheaf returned
  no hit before writing. The exact general comparison declaration found upstream is
  reused, not copied or reproved.

Source checks: read the local Stacks source at `sites-modules.tex`,
`lemma-constant-exact` and `lemma-completion-flat`, and `derived.tex`,
`lemma-right-derived-exact-functor`. They apply without boundedness or finite-generation
conditions on M. No statement correction and no STATEMENT-DISPUTED issue was needed.

## Second reading by Q28

This is the worker's self-check; the brief reserves independent review for the maintainer
and forbids starting another agent. Reopened the node and module and matched the scheme,
adic datum, actual completed coefficient ring and gamma inverse, exactness, localization
factorization, triangulatedness, both comparison orientations and their naturality.
Checked the cohomology constructor's source normalization and the order of the five
isomorphisms defining the shifted-single comparison. No arbitrary map or Nonempty choice
replaces either comparison. The first compile exposed a kernel mismatch in an instance
inferred under generalized local let instances; unfolding the existing derived functor
before inference repaired it. The same compile identified the required `Functor.` prefix
on the whiskering operations. Both were repaired. The general cohomology interface is used directly through the dependency node’s
existing `mathlib_match`, `DerivedCategory.homologyFunctor`; its landed N5 Lean record
is retained unchanged.

## Return repair

Repaired H13 from the independent review of immutable head `b3477c2d3d69`: restored
`def-weil-derived-cohomology-sheaves.json` byte-for-byte from the live repository,
including N5’s `lean` record and all twelve declarations. Removed the dependency-module
repair proposal above. The item module and item Lean record remain unchanged.
The item already imports and uses the dependency’s existing Mathlib match directly;
no rebinding or replacement of the landed N5 module is needed.
