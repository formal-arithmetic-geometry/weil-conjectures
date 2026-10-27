## Worker report

This delivery states `lem-sfb-closed-test-scalar-model-coherence` as
`AlgebraicGeometry.ProEtale.ClosedTestScalarModelCoherence.closed_test_scalar_model_coherence`
in `Sheaf.Paper.ClosedTestScalarModelCoherence`. It has one proof, exactly `by sorry`.
Two definition modules give the missing explicit diagram predicates and actual model
arrows. All their data are fully defined; no coherence equation is assumed in the
resolution data. No statement correction or disputed statement is needed.

### Hypotheses and objects, clause by clause

- The explicit universe is `u`: schemes and A live in u, the pro-etale site has
  object universe u+1 and morphism universe u, and section groups are `Ab.{u + 1}`.
  We do not identify the site's two universes. The unbounded derived categories
  are the published categories of these internal modules.
- `Λ S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}`, each with `MonObj` and
  `IsCommMonObj`, are the commutative condensed coefficients. This is the underlying
  unbundled encoding of `Profinite.CondensedRing`; `S` denotes the node's Λ'.
- `condensedRingObj Λ X` is exactly the recorded pulled-back coefficient object.
  `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)` is the
  internal module category. `CondensedRing.upperStar` is its exact inverse image;
  `CondensedRing.moduleObjectDerivedPushforward` is its ordinary unbounded derived
  direct image. No derived tensor category replaces these categories.
- `A : Type u`, `[CommRing A]`, `a : Ideal A`, `Spec (.of A)` and `closedMap A a`
  give A, its ideal, U and the actual quotient closed immersion Z→U.
- `V : (Spec (.of (A ⧸ a))).AffineProEt` is the affine ind-etale test;
  `liftedTest A a V` is the specified affine closed-site functor applied to V,
  viewed in the small pro-etale site. Its underlying scheme is B.
- `[IsWContractibleRing Γ(V.left, ⊤)]` and
  `[IsWContractibleRing Γ((liftedTest A a V).left, ⊤)]` are precisely the two
  w-contractibility hypotheses. There are no hypotheses on the fibres T or T0
  being contractible.
- `{X XZ : Scheme.{u}} [IsAffine X]`, `f : X ⟶ Spec (.of A)`,
  `h : XZ ⟶ X`, `fZ : XZ ⟶ Spec (.of (A ⧸ a))`, and
  `w : IsPullback h fZ f (closedMap A a)` give the affine map and cartesian square.
  XZ is allowed to be any specified pullback, canonically identified with the
  chosen fibre product. Its affineness follows from the cartesian square, and is
  not a missing assumption.
- `testFibre f (liftedTest A a V)` is T as a test over X.
  `testFibre fZ (closedTest A a V)` is T0 over XZ. The actual closed fibre arrow
  is the published `testArrow A a w V`. `fibreSectionArrow` makes it a site arrow
  T0→XZ×_X T, with the pullback universal property and its actual projections.
- `c : Λ ⟶ S` with `[IsMonHom c]` is the ring-object morphism. Ordinary restriction
  is the existing `Mod.comap (coefficientMap c X)`; `restrict c X` is its existing
  exact derived functor, not a chosen equivalence.
- Every object to which the closed model assertion applies is in
  `DerivedCategory.Plus`: `N` over S and `K` over Λ. The output direct images and
  equations remain in the full unbounded categories. An actual map is bound as
  `α : K.obj ⟶ (restrict c X).obj N.obj`, not a cohomology map or an existence claim.
- `TestModel R h K` contains a K-injective I, an isomorphism QI≅K, a K-injective J
  and a quasi-isomorphism j:h*I→J. It does not assume any of the conclusions.
  All these choices are universally quantified. A restricted S-K-injective is
  never asserted to be Λ-K-injective: `P` is a separate Λ-resolution.

### Every conclusion clause

1. Delta is the already published `ClosedTestDerivedExchangeModel.restrictPush c b`.
   In functor order its type is `RbS ⋙ ResY ⟶ ResX ⋙ RbΛ`, i.e. exactly
   ResY RbS→RbΛ ResX. Gamma is `gamma c W`, made by `rightDerivedPullback`
   from the literal identity of underlying sections. Neither is replaced by an
   arbitrary transformation or an inverse.
2. The first conjunct of `UniversalCoherence` is the delta computation-unit equation
   for every complex, with the exact-Q factors and the termwise
   `CondensedRing.comapLowerStarIso`. The first conjunct of `SectionCoherence` is
   the corresponding gamma equation. These are the universal normalization,
   including complexes whose restriction needs another K-injective resolution.
3. The second and third conjuncts of `UniversalCoherence` are the derived unit
   and counit equations, using `ClosedTestDerivedExchangeModel.adj` and the
   existing `CondensedRing.derivedComapUpperStarIso`. Its fourth is compatibility
   with the recorded ordinary pullback compositor `pullComp` descended through Q.
   Its fifth is the full forward delta/derived-mate rectangle for every commuting
   square, with the two coefficient/pullback identifications explicitly present.
   The mate is the existing `ClosedTestDerivedExchangeModel.exchange`.
4. `sectionArrow` is the actual ordinary geometric adjunction unit, evaluated at W,
   followed by `pushEvaluation` and the actual site restriction `evaluationMap t`.
   The second conjunct of `SectionCoherence` is its ordinary coefficient square;
   its third is its right-derived square. Taking b=s and the recorded closed-site
   arrow gives exactly F(B)→(s*F)(V). Its fourth conjunct is the square for the
   direct-image section identity, using the canonical `derivedPushEvaluation`.
5. `ModelCoherence` asserts invertibility of both `sourceModel` and both
   `targetModel` arrows. `sourceModel` is in the forward unit direction:
   Q of the actual `closedUnitComplex`, then the evaluation computation unit,
   then the exact inverse-image of the actual direct-image representative.
   Its inverse therefore has precisely the node's closed-unit-inverse normalization.
   `targetModel` uses the evaluation unit and direct-image representative.
   The four `localizationModel` arrows are also asserted invertible; these are
   the existing degreewise identity on sections, not chosen isomorphisms.
6. `modelCoefficient` is the computation unit over S, the supplied representative
   of N, forward gamma, the inverse of the supplied QP≅ResN, and the K-injective
   computation isomorphism over Λ. `targetModelCoefficient` additionally inserts
   the prescribed exact pullback/coefficient identification. Inverting these
   representation isomorphisms does not invert delta or gamma.
   `sourceCoefficient` is forward gamma followed by θ_s and s*delta_f;
   `targetCoefficient` is forward gamma followed by delta_fZ and RfZ*θ_h.
7. The next two clauses of `ModelCoherence` are the scalar squares for the source
   and target normalized models. The following clause is the chain square for
   `chainRestriction`, literally Q of the degreewise `sectionArrow` composed
   with j evaluated on T0. It is Q(j(T0)η_a), with the actual closed test arrow.
8. The last two clauses of `ModelCoherence` are the source and target localization
   squares, with `localizedCoefficient` given by gamma at the terminal object
   of the test scheme followed by the exact pullback/scalar comparison. On the
   target the extra θ_h is explicitly retained. Together with clauses 2–4 this
   gives localization compatibility for delta and gamma with the degreewise
   section normalization. The recorded localized-site comparison identifies this
   presentation with restriction to the slice site.
9. `MapCoherence` states the actual derived-arrow naturality square and the forward
   gamma cospan square for the closed-test derived section restriction.
   `ModelMapCoherence` adds the five naturality squares for the normalized source
   and target models, their chain restriction and both localized models.
   `modelMap` is defined from the actual derived arrow and the universal computation
   unit; thus no representative of α or extra homotopy choice is assumed. The two
   independent universal clauses (model coefficient squares for N, and model
   naturality for K→ResN) give the node's full mixed-coefficient naturality.
10. The final conjunct specializes to `ClosedTestDerivedExchangeModel.scalarUnit c X M`:
    `singleFunctor` applied to the ordinary `Mod.extendRestrictAdjunction` unit,
    followed by the exact restriction/single comparison. Its target is ordinary
    `Mod.extendScalars M` in degree zero. Both `MapCoherence` and every supplied
    pair's `ModelMapCoherence` are asserted here. There is no derived tensor unit,
    flatness hypothesis, scalar-comparison invertibility or preservation of
    K-injectives by restriction anywhere in the statement.

### Dependency declarations read and used

The declarations' full signatures and docstrings were read in the published sources.
The original statement dependencies are retained unchanged.

| DAG dependency | Module and declarations |
| --- | --- |
| sk-def-sfb-condensed-ring | `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` |
| sk-def-sfb-pulled-back-coefficients | `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `condensedRingObj`, `coefficientPullbackIso`, `condensedPullbackHom` |
| def-weil-pbc-proetale-site | `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology` |
| sk-def-sfb-module-objects | `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod` |
| sk-def-sfb-module-derived-pushpull | `Sheaf.Paper.CondensedModuleDerivedPushpull`: `CondensedRing.moduleObjectDerivedPushforward`, `moduleObjectDerivedPullback`; ordinary `upperStar` and `lowerStar` |
| def-exc-closed-site-lift | `WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteLift`: `Scheme.AffineProEt.closedSiteLift` and its specified inclusion |
| sk-def-pe-wlocal | `WeilConjectures.RingTheory.ProEtale.WContractible`: `IsWContractibleRing` |
| def-pc-fibre-product | Mathlib's `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `IsPullback` |
| def-weil-closed-immersion | `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`; the canonical quotient `Spec.map` is used |
| sk-def-sfb-change-of-scalars | `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`: `Mod.comap`, `Mod.extendScalars`, `Mod.extendRestrictAdjunction` |
| sk-def-sfb-derived-categories | `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` and the canonical upstream `DerivedCategory`, `DerivedCategory.Q` |
| def-sfb-right-derived-functor | Same recorded module and the canonical `Functor.rightDerivedFunctor`, `rightDerivedFunctorUnitQ`, `rightDerivedPullback`, `rightDerivedFunctorObjQIso` |
| def-sfb-proetale-inverse-image-unit-section | `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`: `inverseSection`; the internal actual-unit presentation is the recorded `closedUnitComplex` in the section-model dependency |
| def-pur-localized-ringed-site | `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`: `SheafOfModules.overFunctor`, `over`, `overMap`; the recorded section-model `localizationSections` and `localizationModel` implement its normalized evaluation presentation |

The first new definition node cites the landed
`lem-sfb-closed-test-kinjective-section-models`, whose module
`Sheaf.Paper.ClosedTestKInjectiveSectionModels` supplies `evaluation`, `complexes`,
`pushEvaluation`, `evaluationMap`, `testFibre`, `closedMap`, `closedTest`, `liftedTest`,
`testArrow`, `closedUnitComplex`, `pushModel`, `exactRepresentative`,
`pullRepresentative`, `localizedSections` and `localizationModel`. These are reused
without copying their definitions. Coefficient comparisons are the published
`coefficientMap`, `CondensedRing.comapLowerStarIso`, `comapUpperStarIso` and
`derivedComapUpperStarIso` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`.

The already landed `Sheaf.Paper.ClosedTestDerivedExchangeModel` also supplies
`restrict`, `restrictPush`, `scalarUnit`, `adj`, `pullComp`, `exchange`, and its existing
K-injective-preservation instance for direct image. We use only those independent
constructions; none of its postponed exchange/coefficient theorems is used to define
our data or assumed as a hypothesis. This module's DAG node is a consumer of this item,
so it is deliberately not made a new DAG dependency: that would create a cycle. Per
stages/2-statements.md §3(7), the maintainer must OMIT the future reverse proof import
of this item into `ClosedTestDerivedExchangeModel`, because it would close an import
cycle. This is an explicit listed import omission, not a dependency wait.

The main module imports the available proof-dependency modules
`ExactSquareRightDerivedUnit`, `InternalSectionScalarAdjunction`,
`SectionDerivedPushpullNormalization`, `ProEtaleRingSheafChangeAdjunction`,
`Sites.UnboundedSectionsLocalization`, `ClosedTestUnitEvaluation`,
`RingedDerivedSliceLocalization` and Mathlib's `DerivedCategory.KInjective` privately.
Coefficient morphisms and scalar adjunctions are already available through the public
support imports. Its nine-step proof docstring follows all nine DAG proof steps.
`lem-sfb-closed-test-chain-mate-restriction` and
`lem-sfb-closed-test-localized-model-coherence` have no current Lean records: their
proof imports are therefore omitted. Their conclusions are not needed as input data
for this statement; the actual maps and diagrams are fully constructed here from the
recorded definitions. There are no missing statement prerequisites or dependency repairs.

### Sources and edge cases

Read Stacks `derived.tex` at the universal K-injective definition/computation (070Y),
K-injective Hom computation (070I), and derived adjunctions (09T5), and
`proetale.tex` at lemma-closed-immersion-affines-apply (09BL). The given node's source
and nine-step proof also specify the scalar/section assembly. Blueprint lookup uses
`literature/blueprint/latest`; the inherited ancestor is null (confirmed by the
blueprint ancestor tool), and the new definitions preserve that route and via chain.

Checked c=id, a=0 (identity closed immersion), a=A (empty closed fibre), the zero
coefficient ring, zero module/object/map, and non-flat Z→Z/2 coefficients. No proper
ideal, nontrivial-ring, nonempty-test, characteristic, perfectness or flatness condition
is present. In the non-flat example restriction of an injective Z/2-module need not be
injective over Z; the construction uses a fresh Λ-K-injective target model and the
forward computation unit, so it does not claim this false preservation. Identity
comparisons are the canonical normalized ones and all degeneracies retain the actual
unit and compositor maps. All equalities are in the full D(Ab), not merely on homology.

### Search evidence

The prescribed msearch wrapper was used for LeanSearch, LeanFinder, Loogle and
Mathlib grep; the exact calls and returned hit names are recorded below and in each
new node's `mathlib_searches`. Local `rg` searched both `lean/WeilConjectures` and
`lean/Sheaf`; exact-id `grep -rn` found no upstream declaration of this item.
The broader local search found the existing exchange helpers, and the final files
reuse them. Its old coefficient-naturality theorem does not state the computation-unit
normalizations and representative-level diagrams of this node, so the item is not an
`existing: true` match. Blueprint searches `normalized scalar` and `closed test` both
returned zero; DAG scalar/model searches found this theorem and neighboring lemmas,
not either missing definition predicate.

- Tool `loogle`, query `"rightDerived", "restrictScalars"`: 0 hits; none.

- Tool `leanfinder`, query `Restriction of scalars on pro etale module sheaves commutes with closed test section models and derived adjunction mates`: 8 hits; `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`, `SheafOfModules.restrictScalars`, `AlgebraicGeometry.Scheme.Modules.restrictAdjunction_counit_app_app`, `SheafOfModules.restrictScalars_obj_val`, `SheafOfModules.restrictScalars_map_val`, `AlgebraicGeometry.Scheme.Modules.instIsLeftAdjointRestrictFunctor`, `AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app`, `ModuleCat.Tilde.res_apply`.

- Tool `grep`, query `(restrictScalars|restrictionOfScalars).*(rightDerived|baseChange|unit)|(rightDerived|baseChange|unit).*(restrictScalars|restrictionOfScalars)`: 25 hits; `Mathlib/Analysis/Normed/Module/Basic.lean`, `Mathlib/Analysis/Normed/Module/Basic.lean`, `Mathlib/Analysis/Normed/Module/Basic.lean`, `Mathlib/Analysis/Normed/Module/Basic.lean`, `Mathlib/RingTheory/Localization/BaseChange.lean`, `Mathlib/RingTheory/Localization/BaseChange.lean`, `Mathlib/RingTheory/IsTensorProduct.lean`, `Mathlib/RingTheory/IsTensorProduct.lean`.

- Tool `leanfinder`, query `Restriction of scalars commutes with derived sections and closed test section models universal right derived comparison`: 8 hits; `CategoryTheory.LocalizerMorphism.rightDerivedFunctorComparison`, `SheafOfModules.restrictScalars`, `PresheafOfModules.restrictScalarsCompToPresheaf`, `SheafOfModules.restrictScalars_obj_val`, `PresheafOfModules.Derivation.Universal.desc`, `CategoryTheory.LocalizerMorphism.rightDerivedFunctorComparison_fac`, `SheafOfModules.restrictScalars_map_val`, `PresheafOfModules.restrictHomEquivOfIsLocallySurjective`.

- Tool `loogle`, query `"rightDerived", "restrictScalars"`: 0 hits; none.

- Tool `grep`, query `(restrictScalars|restrictionOfScalars).*(rightDerived|baseChange|unit)`: 21 hits; `Mathlib/Algebra/Category/ModuleCat/Monoidal/Adjunction.lean`, `Mathlib/Algebra/Category/ModuleCat/Monoidal/Adjunction.lean`, `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`, `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`, `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`, `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`, `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`, `Mathlib/Algebra/Star/Subalgebra.lean`.

- Tool `leansearch`, query `Canonical forward restriction of scalars comparison for total right derived direct image and derived sections without flatness`: 8 hits; `PresheafOfModules.restrictScalarsObj`, `ModuleCat.RestrictScalars.obj'`, `ModuleCat.instIsRightAdjointRestrictScalars`, `SheafOfModules.restrictScalars`, `PresheafOfModules.restrictScalars`, `ModuleCat.restrictScalars`, `ModuleCat.RestrictScalars.map'`, `CategoryTheory.Functor.totalRightDerived`.

- Tool `leansearch`, query `Canonical normalized scalar restriction comparison between K injective section models at closed pro etale test objects`: 8 hits; `Module.RestrictScalars.normedSpaceOrig`, `NormedSpace.restrictScalars`, `instSeminormedAddCommGroupRestrictScalars`, `IntermediateField.coe_restrictScalars`, `IntermediateField.restrictScalars_inj`, `Submodule.restrictScalars_injective`, `ContinuousLinearMap.coe_restrictScalarsIsometry`, `RestrictScalars.normedSpace`.

- Tool `leanfinder`, query `Restriction of scalars commutes with normalized K injective closed test section model chain restriction diagrams`: 8 hits; `AlgHom.restrictNormal_comp`, `ModuleCat.restrictScalarsComp'App_inv_naturality`, `ModuleCat.restrictScalarsComp'App_hom_naturality`, `ModuleCat.restrictScalarsComp'App_inv_naturality_assoc`, `ModuleCat.restrictScalarsComp'App_hom_naturality_assoc`, `HomologicalComplex.restrictionMap_f'`, `NormedSpace.restrictScalars_eq`, `ModuleCat.restrictScalarsComp'_inv_app`.

- Tool `grep`, query `closed.*[Ss]calar|[Ss]calar.*closed` in `CategoryTheory`: 0 hits; none.

## New nodes

`def-sfb-closed-test-scalar-comparison-maps` owns
`Sheaf.Paper.ClosedTestScalarComparisonMaps`. It defines the missing evaluation gamma,
actual section restriction and derived direct-image evaluation comparison, and the
explicit predicates `UniversalCoherence` (five families of equations) and
`SectionCoherence` (four). The ordinary restriction abbreviation expands directly to
the published `Mod.comap`; the existing direct-image scalar comparison, derived scalar
restriction, scalar unit and mate are imported instead of duplicated. Sources are
Stacks 070Y, 09T5, 07A6, 0D6D–0D6F and the item's scalar/section assembly. The recorded
LeanSearch/LeanFinder/Loogle, Mathlib and project grep, DAG and blueprint searches found
no existing definition of these simultaneous normalized diagram predicates. Its node
cites all foundational notions it uses, including the published closed-test evaluation
models; it asserts no equation as a theorem.

`def-sfb-closed-test-scalar-model-diagrams` owns
`Sheaf.Paper.ClosedTestScalarModelDiagrams`. It defines `TestModel`, the actual
`fibreSectionArrow`, chain restriction, forward normalized source and target models,
forward coefficient and actual-map model arrows, and `ModelCoherence`, `MapCoherence`,
`ModelMapCoherence`. The node spells out the normalization, all scalar squares and all
five model naturality squares. Sources are Stacks 070I, 070Y, 09T5, 09BL and 0D6F,
assembled exactly for this item's two closed tests. Searches found the published
individual representative/localization arrows and the neighboring theorems, which
are reused, but no bundled representative data plus these explicit scalar diagram
predicates. Definitions contain no existence choice or postponed data. Both new nodes
are cited directly by the item and have empty proof and proof-dependency lists.

## Second reading by Q71

The dispatch forbids starting other agents, and specifies the maintainer's independent
review after delivery. This is therefore a second complete reading by the same
worker, with the original node, the three Lean files and both new node records open;
it is not represented as an independent agent review.

I checked every hypothesis against the list above: the coefficient ring objects and
morphism, site and section universes, ideal including both extreme ideals, exact
coefficient restriction, affine f, specified cartesian square, the actual lift and
both contractibility instances, bounded-below inputs, supplied K-injective models,
and every actual derived map. No assumption on scalar invertibility or preservation
of K-injectives appears. The source/target types of the unit, counit, compositor and
mate equations agree with the node's forward delta direction. I checked each of the
five UniversalCoherence equations, four SectionCoherence equations, the eight model
isomorphism assertions, five scalar model squares, two actual-map cospan equations,
five ModelMapCoherence equations, and the final ordinary scalar-unit specialization.
The source model is forward; its inverse has the required closed-unit-inverse
normalization. The localization arrows use the recorded literal section identity.

Changes from this reading: removed duplicate definitions of the published scalar
restriction, direct-image comparison, ordinary scalar unit, adjunction, pullback
compositor and exchange; the final files use the existing declarations. Added the
four explicit localization-model invertibility conclusions alongside their squares.
Split helpers into two genuine definition modules to keep single-file elaboration
within 60 seconds. Shortened the one newly exposed overlong line. The old draft and
old report describing abandoned interfaces have been removed/replaced. New-node
statements, their dependency citations and stored Lean signatures were checked
against the final definitions. The original item's statement and proof are unchanged;
only its lean field and the addition of the two definition dependencies change.

Compilation uses only scompile.py against the live server. All three final modules
are checked separately, including their importable library names and dependency
order. Dry-run and delivery outcomes are recorded after running the prescribed wrapper.

First dry run: server preflight required `import_flags` on both new definition nodes. Added the empty lists required by the live node schema; no Lean change was needed. All three final files compiled cleanly with scompile.py.
