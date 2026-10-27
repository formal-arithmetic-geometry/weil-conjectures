## Worker report

Item: lem-sfb-qcqs-closed-pullback-finite-model-completion. The module is
`Sheaf.AlgebraicGeometry.QcqsClosedPullbackFiniteModelCompletion`, namespace
`AlgebraicGeometry.ProEtale.QcqsClosedPullback`. Three named theorems, all with `sorry`
proofs, jointly state the node. There is no statement correction, dependency repair,
or new independent notion. Helpers merely name the already defined module category,
exact integral pullback and its supplied structures, and projections from the existing
Roos complex. All their data is explicit; none selects data from a postponed existence.

Hypotheses and clauses:

- The arbitrary commutative condensed ring is the explicit sheaf `Λ` with `[MonObj Λ]`
  and `[IsCommMonObj Λ]`. It need not come from a topological ring. `Modules Λ X`
  unfolds to internal modules over the existing `condensedRingObj Λ X`, i.e. p_X^*Λ.
- `i : Z ⟶ V` with `[IsClosedImmersion i]` is precisely the closed immersion.
  `[CompactSpace V] [QuasiSeparatedSpace V] [CompactSpace Z] [QuasiSeparatedSpace Z]`
  express qcqs on both schemes. `_hc : IsCompact (Set.range i)ᶜ` is exactly the
  quasi-compact complementary open. No chosen complementary open scheme is required.
- All schemes have universe u, the small pro-etale site has objects in u+1 and
  morphisms in u, and coefficient abelian groups are `Ab.{u+1}`. `Derived` is the
  ordinary unbounded `DerivedCategory`; it is not a completed category. There is no
  equality imposed on the site object and morphism universes and no boundedness binder.
- Exact inverse image is the recorded `CondensedRing.upperStar Λ i`. Its existing
  exactness instances are imported. The derived operation is the recorded
  `moduleObjectDerivedPullback Λ i`, canonically compared to termwise pullback by
  `leftDerivedUpperStarIsoMapDerivedCategory`.
- In `finite_models_constructible_tor`, the first conjunct quantifies over the specified
  pro-etale cover 𝒰 and its finite scalar presentation modules P. The two assumptions
  are `Mod.IsFinitelyPresented Λ (P a)` and the original local-model isomorphisms.
  The conclusion uses exactly `𝒰.pullback₁ i`, with the same P a, so it preserves
  the scalar models on the pulled-back cover, rather than just asserting that some
  unrelated local models exist.
- Its second conjunct uses the dependency's exact predicate
  `IsConstantModelConstructible`, before and after `upperStar`.
- Its third conjunct is preservation of the object property defining D_ctf:
  `constantModelBoundedConstructible ∧ DerivedCategory.finiteTorAmplitude`.
  Its fourth conjunct separately preserves every `torAmplitudeIn _ a b` with the
  identical integers a,b; no widening, order assumption or nonzero-object assumption.
- Its final conjunct asserts `IsIso` of the actual composite: the published
  `leftDerivedUpperStarTensor` at K and `singleFunctor 0 (lowerStar i N)`, then the
  exact derived pullback comparison, the single-degree comparison, and the image
  of `upperStarLowerStarAdjunction.counit.app N` under `singleFunctor 0`, tensored
  on the left by i^*K. Thus the input is ordinary i_*N in degree zero, and the
  resulting map has target i^*K tensor N[0]. It is not Ri_*N or an arbitrary iso.
- The integral specialization explicitly binds `l : ℕ`, `[Fact l.Prime]`, the field E,
  `[Algebra (Padic l) E]` and `[FiniteDimensional (Padic l) E]`. The integer ring,
  its norm topology, chosen uniformizer and quotient sheaves are precisely those
  of DerivedNakayama/AdicCompletion; no alternate ring or topology is supplied.
- `normalized_strict_completion` chooses coefficient isomorphisms c whose underlying
  abelian map is explicitly the coefficient/point inverse-image comparison. For every
  unbounded complex P, b is pinned degree by degree to the inverse ordinary tensorator
  followed by c. Its next equations preserve the actual `levelStep` and `levelUnit`.
- The same theorem provides a single chain isomorphism e between the pulled-back
  existing Roos complex and the Roos complex of pulled-back P. Its first-coordinate
  projection to every quotient level is i^* of that projection followed by b.
  The second-coordinate equation states exactly the same product comparison in
  degree k-1. The helpers `roosFirstEvaluation` and `roosSecondEvaluation` are literal
  biproduct projections followed by product projections, with explicit types to
  avoid expensive elaboration of the integral coefficients. These equations pin
  the canonical product map in both coordinates, including its off-diagonal zeros.
- The equation with `AdicCompletion.augmentation` fixes the map (unit,0); that
  dependency's augmentation is explicitly defined by `biprod.lift (unitProduct.f k) 0`.
- For any regular-module d satisfying the explicit section formula for the chosen
  uniformizer and n≥1, the regular comparison intertwines d^n on the two sides.
  `integralRegularComparison` is the existing scalar-matrix regular comparison
  composed with the dependency's regular point-pullback identifications. Together
  with c and the level-unit equations, this is preservation of the specified
  two-term resolution [A --pi^n--> A] and its actual quotient augmentation.
- For any K and any K-flat P representing it, the same e is localized to the
  completion comparison c. The signature explicitly fixes aZ to the canonical
  exact-localization comparison and fixes c to Q(e) composed with the same exact
  comparisons. It asserts that pulled-back P is K-flat and that i^* of the actual
  `completionMap` followed by c equals the actual `completionMap` of i^*K.
  `AdicCompletion.roos_isDerivedLimit` identifies these existing Roos objects with
  Rlim Res_n(K tensor^L P_n), with the actual quotient adjunction units. Thus the
  displayed comparison is the node's derived-limit comparison with its normalization.
- `derived_completion` finally states `IsDerivedComplete l E V K →
  IsDerivedComplete l E Z (moduleObjectDerivedPullback.obj K)` for every unbounded K.
  The normalized comparison is stated even when K is not complete, as in the node.

Dependency declarations used (module paths abbreviated only in this report):

- Sheaf.Paper.CondensedModuleDerivedPushpull:
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback; publicly
  retains the general derived pushpull and adjunction interfaces.
- Sheaf.Topology.ProfiniteCondensedRing: Profinite.CondensedRing, and its underlying
  explicit commutative ring-object encoding used as Λ.
- Sheaf.Paper.CondensedConstantConstructibility:
  AlgebraicGeometry.ProEtale.HasFiniteConstantLocalModel,
  IsConstantModelConstructible, constantModelBoundedConstructible,
  ConstantModelConstructibleFiniteTor. The first cover clause expands the first
  predicate to retain the prescribed cover and same scalar modules.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion;
  Mathlib.AlgebraicGeometry.OpenImmersion: IsOpenImmersion (the complement is
  specified as a compact open subset); Mathlib.Topology.Defs.Filter: CompactSpace;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated: QuasiSeparated and its
  QuasiSeparatedSpace interpretation.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite: Padic's actual finite
  coefficient-extension rings; the uniformizer is coefficientExtensionUniformizer.
- Sheaf.SixFunctors.ProEtale.DerivedCompletion:
  AlgebraicGeometry.ProEtale.IsDerivedComplete and AdicCompletion.Modules,
  finiteModule, level, levelStep, levelUnit, product, roos, augmentation,
  completionMap, and roos_isDerivedLimit.
- WeilConjectures.CategoryTheory.Triangulated.DerivedLimit: IsDerivedLimitTriangle;
  WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism:
  towerTransitionEndomorphism. These occur in the existing Roos construction and
  its identification, which this module reuses.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings: restrictScalars is the
  sectionwise restriction; the ordinary internal restriction in the recorded
  completion interface is Mod.comap.mapDerivedCategory, retained through its imports.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom and .Tensor:
  the existing relative derived monoidal structure, derivedTensor and derivedHom.
  WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude: torAmplitudeIn,
  finiteTorAmplitude, with ordinary degree-zero sheaf tests.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs:
  upperStar, lowerStar, upperStarLowerStarAdjunction and its exactness instances;
  .Derived.UpperLowerStar: leftDerivedUpperStarIsoMapDerivedCategory;
  .Derived.Monoidal: leftDerivedUpperStarTensor;
  .UpperLowerStar.MonoidalModule: monoidal_upperStar.
- Sheaf.Paper.ProfinitePointPullback: profinitePointModuleForgetPullbackIso;
  module-object Basic: condensedRingObj and upperStarFromPointComp.
- Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage:
  scalarMatrixRegularPullbackIso, scalarMatrix_inverseImage.
- Sheaf.Paper.DerivedNakayamaResolution: integerRing, quotientModule, pullback,
  regularPullbackIso and derived_nakayama_resolution.
- The proof-only imports name every stated proof dependency: InternalModuleOperationsTransport,
  InternalSectionTensorComparison, ProEtaleImmersionLimitPreservation,
  ProEtaleRingedClosedCounit, ProEtaleCountableProductsExact,
  ExactProductFunctorStrictLimit and PrincipalReductionDerivedNormalization; Mathlib
  ExactFunctor, FinitePresentation, Fpqc, WeaklyEtale, Proper, and
  ShortComplex.PreservesHomology supply the recorded mathlib matches. Alpha and
  open-immersion base change are already in the public dependency closure.

Source checks: read the node and all statement dependencies, their records, full source
interfaces and docstrings. Read Stacks proetale.tex lemma-closed-immersion-affines-apply
(09BL) and lemma-naive-completion (099M). 09BL supplies closed inverse image and the
closed counit; 099M gives the unbounded derived quotient-tower completion. The finite
model and normalization assembly is exactly the extracted proof recorded in this node.
The old example CompactObject module is withdrawn; followed its current upstream
replacement and the unchanged module-mode/docstring conventions.

Edge cases checked: empty schemes and empty cover indices; zero ring and zero module;
zero finite-presentation ranks; identity closed immersion and empty/full complements;
all integer Tor intervals including a>b (zero-object case); unbounded K and non-complete
K in the comparison; every positive quotient power indexed by n+1, including first
reduction n=0; the resolution statement uses n≥1. The chosen scalar formula for d
retains the specified uniformizer. No extra finiteness or separatedness beyond qcqs,
no Noetherian hypothesis and no boundedness of the complete K were introduced.

Searches (2026-10-22):

- msearch.py leansearch: “Exact inverse image along a closed immersion preserves
  constructible modules and derived completion”: eight hits, closed-immersion geometry
  and constructible-preimage facts; no statement matching this node.
- msearch.py leanfinder: “Closed immersion pullback preserves finite constant
  constructible models Tor amplitude and derived adic completion”: eight hits,
  closed-immersion and immersion base-change facts; no completion or scalar-model result.
- msearch.py loogle: “AlgebraicGeometry.IsClosedImmersion, DerivedCategory”: zero hits.
- msearch.py grep: “constructible.*pullback|pullback.*completion|Roos” in
  Mathlib/AlgebraicGeometry: zero hits.
- rg of lean/WeilConjectures and lean/Sheaf for closed constructible/completion and
  pullback-completion: found etale closed constructibility, generic exact-functor and
  strict-Roos tools, and other completed-tower interfaces; none states this node on
  ordinary internal-module derived categories with these coefficients/normalizations.
- grep of the blueprint id in lean/WeilConjectures: no match. rg of the proposed
  namespace/declaration names in source, Sheaf and dag/lean_names_upstream.json: no match.

Validation: only scompile.py used; final module passed both sandbox compilation (49.2 s)
and its final library-module/artifact compilation (36.3 s), no errors or warnings.
Earlier elaboration timeouts were repaired by explicit regular point-pullback
identifications and typed coordinate helpers; no compile time limit was increased.
All three postponed theorems have this node and source/proof docstrings. The node's
original statement, split and dependencies are unchanged; only its lean record changes.

## Second reading by Q89

The dispatcher prohibits spawning another agent, so this section records a separate
rereading by this worker, not a claim of an independent second worker. The maintainer's
independent delivery review remains the second-person check.

Reopened the node and final file side by side. Matched the general condensed ring and
commutativity to Λ/MonObj/IsCommMonObj, the two qcqs schemes to CompactSpace and
QuasiSeparatedSpace, and the complement to IsCompact(range i)^c. Checked that the first
conjunct retains the same P on the actual pullback cover, and that the two constructible
predicates are the recorded ones. Checked a,b are unchanged and the tensor arrow uses
ordinary i_*N in degree zero. Checked the completion part quantifies over unbounded K,
uses the original quotient objects, and has equations fixing both coordinates and the
(unit,0) augmentation. A preliminary draft allowed an unrelated e in the localized
completion statement; repaired it so c is explicitly the localization of the very e
whose coordinates the same existential specifies. A preliminary regular-map formula
relied on costly definitional equality of point pullbacks and regular modules; replaced
it by the explicit composed regular isomorphism, and restricted its scalar test to the
stated uniformizer powers n≥1. Checked the integral topology is inherited from the
spectral absolute value, not an independent choice. Read every helper body: all merely
compose or project existing data. No remaining statement mismatch was found.
