## Worker report

The module `Sheaf.Paper.FiniteCoefficientDerivedModelComparison` states
`AlgebraicGeometry.ProEtale.finite_coefficient_derived_model_comparison` with one `sorry`.
It states the two natural comparisons together with their canonical normalization formulas.
It introduces no definitions, choices of objects, additional nodes, or dependency repairs.
The item's natural-language statement, dependencies and proof are unchanged.

The source read was Stacks `sites.tex`, example-constant-sheaf (0H7J),
proposition-functoriality-algebraic-structures-topoi (00YV), `derived.tex`,
lemma-right-derived-exact-functor (015F), and `categories.tex`,
lemma-properties-left-localization (04VG). I also read the current blueprint's
sec-proetale-coefficients/sk-thm-pe-direct-image-comparison/
lem-weil-pbc-comparison-pullback.proof.md, especially its final exact-complex sentence,
and the three private comparison constructions at lines 126–170 of
`Sheaf/Paper/FiniteFieldStratifiedPerfectModels.lean`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A finite commutative discrete ring is `B : Type (u + 1)`, `[CommRing B]`, `[Finite B]`,
  `[TopologicalSpace B]`, `[DiscreteTopology B]`. There is no field or nonzero-ring assumption.
- An arbitrary scheme morphism is `{U X : Scheme.{u}} (f : U ⟶ X)`; the constant-complex
  clause separately quantifies over every `T : Scheme.{u}`. There is no properness,
  Noetherian, quasi-compactness, or etaleness hypothesis on these schemes or on `f`.
- The small sites are the recorded `T.smallEtaleTopology` and `Scheme.ProEt.topology T`.
  The module categories, coefficient sheaf and realization are the recorded
  `FiniteCoefficientModules`, `finiteCoefficientRingSheaf` and `finiteCoefficientRealization`.
  In particular the latter realizes through `finiteCoefficientScalarMap`, the actual
  constant-section map into sheafified continuous functions on connected components.
  No arbitrary coefficient equivalence is supplied as an extra input.
- `N_T` is the existing `finiteCoefficientComparison T B`; its derived functor is the
  existing `finiteCoefficientDerivedComparison T B`. These use `comparisonUpperStar`
  followed by the specified realization and exact termwise localization.
- `F_f` and its derived functor are the existing `finiteCoefficientPullback X B f` and
  `finiteCoefficientDerivedPullback X B f`, publicly reexported by the recorded operations
  module. They are conjugation by the chosen realization and its inverse. This uses the
  supplied finite-ring presentation, without imposing an equality of site universes.
- The first derived isomorphism is the existential natural isomorphism `beta` between
  `finiteCoefficientDerivedComparison X B ⋙ finiteCoefficientDerivedPullback X B f` and
  `(Etale.upperStar (ModuleCat B) f).mapDerivedCategory ⋙ finiteCoefficientDerivedComparison U B`.
  Lean writes composition in application order, opposite the paper's function notation.
  Its isomorphism type includes naturality in every derived object and derived morphism.
- The auxiliary existential module natural isomorphism `b` specifies the normalization:
  its equality first whiskers the inverse of the realization equivalence's `unitIso` to
  cancel `E_X^{-1} E_X`, then whiskers `comparisonUpperStarCompUpperStarIso` by `E_U`.
  This existing site isomorphism has direction `nu_X^* ⋙ f_proet^*` to
  `f_et^* ⋙ nu_U^*`, namely the inverse of the comparison denoted `c_f` in the node proof.
- The equality for `beta` is exactly the inverse derived-composition isomorphism,
  `Functor.mapDerivedCategoryNatIso b`, and the derived-composition isomorphism on the
  other side. The imported exact-derived APIs normalize these through
  `mapDerivedCategoryFactors`, so this specifies localization of the actual termwise `b`.
- Underlining of an arbitrary integer cochain complex is
  `(constantSheaf ... (ModuleCat.{u + 1} B)).mapHomologicalComplex (ComplexShape.up ℤ)`.
  `P : CochainComplex (ModuleCat.{u + 1} B) ℤ` is unrestricted: there is no finite,
  finitely generated, perfect, projective, bounded, or bounded-below condition.
- The second comparison is the natural isomorphism `gamma` of functors from the entire
  category of such cochain complexes to `FiniteCoefficientDerivedCategory T B`.
  Its source is termwise etale constants, then `DerivedCategory.Q`, then `N_T^D`;
  its target is termwise pro-etale constants, then `DerivedCategory.Q`, then `E_T^D`.
  This gives the displayed isomorphism of whole derived objects at every `P`, and its
  natural-isomorphism type enforces naturality for every chain map.
- The equality at every `P` specifies the second normalization: the derived composition
  comparison at the etale constant complex, realization of the localization factor for
  `comparisonUpperStar`, and realization of `Q` of
  `Functor.mapHomologicalComplexCompIso (comparisonUpperStarConstantSheafIso B T)`.
  This is the same composite as the reference's `comparisonConstantComplexIso`.
- That last chain isomorphism applies the canonical module-constant comparison in degree
  `q` to `P.X q`. Its components are the components of the module natural isomorphism,
  by Mathlib `Algebra/Homology/Additive.lean:165–220`. Naturality at `P.d q (q+1)`
  is its chain-map square, and naturality at every component of a chain map is preserved.
  Thus the signature specifies actual differentials, not just graded terms.

Dependency declarations read and used, directly or through public reexports:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, with its actual morphisms.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: the coefficient ring sheaf, module
  category, realization, comparison and exact derived comparison named above.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparisonModules`,
  whose inverse image is exactly `ProEtale.comparisonUpperStar`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: publicly reexports
  `ProEtaleIntrinsicFiniteOperations`, in turn reexporting
  `ProEtaleFiniteCoefficientDirectImage`, which defines `finiteCoefficientPullback`,
  `finiteCoefficientDerivedPullback`, and the realization equivalence used in the signature.
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`:
  `CategoryTheory.constant_left_module_inverse_image`, for proof step 1.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategoryFactors`, the exact factorization leaf.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `supportSiteComparison_pullback_coherent` and its underlying canonical pullback map;
  the signature uses `comparisonUpperStarCompUpperStarIso` from
  `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic`, the inverse orientation.
- `Mathlib.CategoryTheory.Localization.Predicate`: `CategoryTheory.Localization.liftNatIso`,
  used by `mapDerivedCategoryNatIso` from the upstream ExactFunctor module.
- `Sheaf.CategoryTheory.ExactDerivedComposition`:
  `CategoryTheory.Functor.existsUnique_mapDerivedCategoryCompIso`, which characterizes
  the upstream `mapDerivedCategoryCompIso` used in the normalization formulas.
- `Sheaf.SixFunctors.GeometricInverseImageConstantModule`:
  `CategoryTheory.geometric_inverse_image_constant_module`; its scheme comparison
  specialization is `comparisonUpperStarConstantSheafIso` from the upstream
  `WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf` module.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.isContinuous_overPullback` and `Etale.upperStar`.
- `Sheaf.CategoryTheory.SiteInverseImageTensor`: `CategoryTheory.siteInverseImage_tensor`.
  All stated proof dependencies are imported, including those used only by the proof plan.

Edge cases checked mathematically against the constructions: the zero ring is allowed;
empty schemes and empty covers introduce no nonemptiness binder; identity morphisms and
arbitrary scheme morphisms retain the canonical comparisons; zero complexes and zero terms
are allowed; infinite modules, nonprojective modules, and complexes unbounded in both
integer directions occur in the quantified source category. Scheme sites retain object
universe `u+1` and morphism universe `u`; coefficients and module values use the published
`u+1` convention. `autoImplicit false` binds every variable explicitly.

Searches actually run:

- `msearch.py ... leanfinder "Canonical derived etale proetale finite coefficient comparison
  commutes with pullback and sends arbitrary constant cochain complexes to constant complexes
  naturally"`: 8 hits, all standard-etale ring presentation results; no match.
- `msearch.py ... loogle "CategoryTheory.Functor.mapDerivedCategoryNatIso,
  CategoryTheory.Functor.mapDerivedCategoryCompIso"`: 0 hits, unknown identifier for the first
  name in Mathlib. Both names were then located and read in the upstream ExactFunctor module.
- `msearch.py ... grep "finiteCoefficientDerived|comparisonUpperStarConstantSheafIso|
  comparisonUpperStarCompUpperStarIso"`: 0 Mathlib hits.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id and proposed theorem
  name found no declaration. Searches for `coefficientComparisonPullbackIso` and
  `comparisonConstantComplexIso` found only the private reference constructions in
  `FiniteFieldStratifiedPerfectModels.lean`; they cannot be named by another module.
  The new module states their assembled result without copying any of those definitions.
- Direct `rg` by the generic derived and constant-comparison names located the upstream
  canonical APIs used in the statement. The Mathlib additive-complex construction was read
  to check that the constant comparison includes differential and chain-map naturality.

Validation: the module passed the prescribed `scompile.py` server compilation as both an
isolated sandbox file and its named library module, with no errors or non-sorry warnings.
The final import uses the recorded operations module, which publicly exposes the same
finite-coefficient interface. No statement dispute or source correction was needed.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
