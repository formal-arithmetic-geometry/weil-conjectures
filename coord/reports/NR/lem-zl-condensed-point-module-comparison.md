## Worker report

The delivery states the full point-module and ordinary unbounded derived comparison.
The item statement, statement dependencies, proof, and proof dependencies are unchanged.
There is one new module, `Sheaf.Paper.CondensedPointModuleComparison`, with five named
Prop-valued theorems whose proofs are `sorry`, and one construction with real data.
No definition contains `sorry`.

The earlier worker's reason for stopping was a stage-1 review by Q156. The live node
indeed has reviewed.result = pass, dated 2026-10-22, but has no lean or reviewed_lean
record. That is a completed split, not a duplicate Lean statement. There is no released
repair note for the item. The current work supplies its missing stage-2 statement.

The ordinary natural isomorphism is NOT defined again:
`AlgebraicGeometry.ProEtale.CondensedRing.upperStarFromPointModComp`, in
`WeilConjectures.WeilObject.Sheaf.Stalk`, already constructs exactly Phi. Its definition
first uses `Functor.mapModCompIso` for the specified `upperStarFromPointComp`, then
cancels restriction and extension along the specified `condensedPullbackHom` using
`Mod.extendScalarsIsoComapInv` and the unit of `Mod.comapEquivalenceOfIsIso`.
The module imports and uses this existing declaration verbatim. That declaration alone
does not cover the node's exactness and derived representative-normalization clauses,
so an existing-only binding of this item would omit those clauses.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| An arbitrary commutative condensed ring Lambda | Every declaration binds `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `[MonObj Λ] [IsCommMonObj Λ]`. This is the unbundled form of `Profinite.CondensedRing`: `Mon.mk Λ` bundles exactly this ring; no topological-ring presentation is assumed. |
| Arbitrary schemes and arbitrary morphism f:T -> X | Explicit `{T X : Scheme.{u}} (f : T ⟶ X)`, with no smoothness, properness, quasi-compactness, flatness or nonemptiness hypotheses. The three point exactness declarations bind an arbitrary `X : Scheme.{u}`, so apply to both T and X. |
| Small pro-etale sites | The underlying categories are `Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}` and the corresponding T category, as in the recorded Mathlib `Scheme.ProEt` dependency. Site objects have universe u+1 and morphisms u; the coefficient universe is u+1. No equality between those universes is added. |
| Inverse image p_Y^* from the point | `upperStarFromPoint Y`; the dependency's `sfbPullbackFromPoint Y` is its transparent alias. Its actual definition is `pointUpperStar ⋙ upperStar Ab (toSpecZ Y)`. |
| Lambda_Y = p_Y^* Lambda | `condensedRingObj Λ Y` is the existing abbreviation for `(upperStarFromPoint Y).obj Λ`, with the actual transported ring structure. No ring or coefficient datum is newly chosen. |
| Specified monoidal comparison phi | `(upperStarFromPointComp f).hom`, the inverse composition comparison followed by the structure-map equality. Its monoidality is the existing `isMonoidal_upperStarFromPointComp` instance. |
| Its coefficient component alpha_f | `condensedPullbackHom Λ f`, definitionally the component of this comparison at Λ, with its existing `IsMonHom` and `IsIso` instances. |
| Point modules and modules on Y | `Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ` and `Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)`, the recorded Mathlib module-object definition. |
| Transport p_{Y,Lambda}^* | Existing `CondensedRing.upperStarFromPointMod Λ Y`, defined as `(upperStarFromPoint Y).mapMod Λ`. The mapMod action is exactly the tensorator followed by the image of the original action, and it commutes with forgetting modules. |
| Module inverse image with coefficient map alpha_f | Existing `CondensedRing.upperStar Λ f`, defined as transport by the abelian inverse image followed by `Mod.extendScalars (condensedPullbackHom Λ f)`. |
| Module inverse image of the pro-etale operations node | Under the node's stipulated internal/sectionwise identification, `InternalModuleOperations.upperComparison Λ f` compares that same internal functor with the sectionwise sheafified tensor pullback. Its exact equivalences are `sectionModuleEquivalence`, and its ring map is induced by the adjoint of the same alpha_f. The general arbitrary-ring-sheaf operations have a lean-only existing-interface repair described below. |
| For every Lambda-module M | `condensedPointModule_comparison_linear` binds arbitrary `M : Mod ... Λ`. |
| Transport source action along alpha_f | The source of its action identity is explicitly `Mod.comap (inv (condensedPullbackHom Λ f))` applied to the two transported module objects. Its underlying sheaf is literally `f^{-1}p_X^* M`, without a tensor-product object in its place. This is canonically the extension-of-scalars presentation by the exact existing scalar-isomorphism cancellation. |
| phi_M is Lambda_T-linear | The conclusion is `Mod.act source.X ≫ phi_M = condensedRingObj Λ T ◁ phi_M ≫ Mod.act target.X`. It is precisely the module-morphism axiom, with alpha_f^{-1} used on the source. |
| These specified maps assemble into Phi | Existing `upperStarFromPointModComp Λ f` is a natural isomorphism of the exact stated functors, using the exact above scalar cancellation. It supplies module-linear inverses and naturality. No existentially arbitrary module comparison is substituted. |
| Exact module functors | `condensedPointModule_preservesFiniteLimits`, `condensedPointModule_preservesFiniteColimits`, and `condensedPointModule_additive` state exactness of point-module pullback. The existing `CondensedRing.upperStar` instances, also summarized by `module_pullback_additive_exact`, give exactness of arbitrary scheme module inverse image. Their composite is exact. |
| Ordinary unbounded derived categories | `DerivedCategory` of these same internal module categories, and `Functor.mapDerivedCategory`; no completion or bounded/full subcategory is used. |
| Derived natural isomorphism Lf^* D(p_X^*) ~= D(p_T^*) | `condensedPointModuleDerivedComparison Λ f` has source `(upperStarFromPointMod Λ X).mapDerivedCategory ⋙ (CondensedRing.upperStar Λ f).mapDerivedCategory` and target `(upperStarFromPointMod Λ T).mapDerivedCategory`. Composition order in Lean is left-to-right. Exact derived inverse image is the total left derived functor by the recorded exact-functor-derived-functor dependency. |
| Apply Phi termwise and localize | The definition is `(Functor.mapDerivedCategoryCompIso ... ...).symm ≪≫ Functor.mapDerivedCategoryNatIso (upperStarFromPointModComp Λ f)`. The existing mapDerivedCategoryNatIso is explicitly `Localization.liftNatIso` applied to `NatIso.mapHomologicalComplex` followed by Q. It is a real construction, not a choice from an existence assertion. |
| Component on every represented complex | `condensedPointModuleDerivedComparison_normalization` binds arbitrary `K : CochainComplex (Mod ... Λ) ℤ`. Its equality says derived comparison followed by the target Q-factorization equals the iterated source Q-factorizations, termwise-composition identification, and `Q.map` of the chain comparison `NatIso.mapHomologicalComplex (upperStarFromPointModComp Λ f) (.up ℤ)`. |
| Degree-n component before localization is phi_{K^n} | `NatIso.mapHomologicalComplex` has in degree n the existing `upperStarFromPointModComp` component at `K.X n`. Reading that component's actual definition gives phi_{(K.X n).X} under the specified coefficient cancellation, as in the preceding linearity identity. The termwise-composition identification has identity components. |
| No flatness, boundedness or finiteness | No such typeclass or hypothesis occurs on Λ, M, f, or K. The complex is indexed by all integers. |

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing` identifies the general
  ring-object input; its continuous/topological specializations are not assumed.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and categorical scheme maps.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt` and its topology.
- `Sheaf.AlgebraicGeometry.ProEtalePointPullback`: `AlgebraicGeometry.ProEtale.sfbPullbackFromPoint`
  and its transparent identification with `upperStarFromPoint`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, `upperStarFromPointComp`, `isMonoidal_upperStarFromPointComp`,
  `condensedPullbackHom`, its ring-morphism and isomorphism instances, and
  `coefficientPullbackIso`, all in `AlgebraicGeometry.ProEtale`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, its action-compatible maps
  and module forgetful functor.
- `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula` publicly reexports
  `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`: `Functor.mapMod`, its explicit
  transported action, `mapMod_comp_forget`, and `mapModCompIso`.
- `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction` publicly reexports the
  arbitrary-ring-sheaf operations of `Sheaf.AlgebraicGeometry.ProEtaleOperations`:
  `Scheme.proEtaleRingModulePullback`, `proEtaleRingModuleDirectImage`,
  `proEtaleRingDerivedPullback`, `proEtaleRingDerivedDirectImage`,
  `proEtaleRingDerivedPullbackFactors`, and the canonical module/derived adjunctions.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`
  and the existing `HasDerivedCategory` interfaces.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`, with coefficient
  universe u+1 and the prescribed site object/morphism universes.
- `WeilConjectures.WeilObject.Sheaf.Stalk`: the existing ordinary point-module functor
  `CondensedRing.upperStarFromPointMod` and canonical `upperStarFromPointModComp`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryNatIso`, `mapDerivedCategoryCompIso`, their factorization
  normalizations, and the ordinary Mathlib `mapDerivedCategoryFactors`.
- Proof-only imports retain the stated DAG proof plan: `SiteInverseImageTensor`,
  `SheafTensor`, `ModuleObjects.LiftExact`, `CondensedModulePullbackExact`,
  `InternalModuleOperationsTransport`, `ExactDerivedComposition`, and
  `ExactFunctorDerivedFunctor`. The finite-upper-star exactness, generic module abelianness,
  restricted-transport linearity, scalar cancellation and localization dependencies are
  already in the imported upstream closure (`FiniteCoefficient.UpperLowerStar.Defs`,
  `ModuleObjects.Abelian`, the upstream monoidal Mod API, and Localization.Predicate).

The source was opened locally: HRS PDF pp. 5--6, Section 3 defines the same coherent
profinite point and p_X, and p. 6 states that arbitrary scheme inverse image has
identified coefficients and is exact. The derived localization and composition
signatures were read from the actual pinned Mathlib/upstream source. Docstrings in
the new module carry the item's six-step natural-language proof, distributed across
the exactness, action identity, construction and representative normalization.

Edge cases checked before writing: the zero condensed ring and zero module; empty T
or X whenever a morphism exists; f an identity or arbitrary nonflat morphism; zero
complexes; complexes unbounded in either or both directions; identity coefficient
isomorphism. No condition in a binder excludes these cases. The proof uses that the
coefficient comparison is invertible, not flatness of the scheme morphism or module.
For identity f, the existing canonical comparisons reduce to the ordinary unit
comparisons, and the derived normalization still includes the Q-factorizations.

Searches made:

1. `msearch.py leanfinder`, query "The natural monoidal comparison for scheme pullback
   of condensed modules from a point lifts to an isomorphism of exact module functors
   and to their unbounded derived categories": eight hits, including LightCondensed
   monoidal instances, `Scheme.Modules` pullback pseudofunctor equations and ordinary
   `SheafOfModules` pullback isomorphisms. No full match to the point/derived normalization.
2. `msearch.py leanfinder`, query "The exact functors induced by inverse image from
   the profinite point commute with scheme inverse image on unbounded derived categories,
   using the given monoidal comparison termwise": eight hits, including generic
   `Functor.mapDerivedCategoryFactors`, `mapDerivedCategoryFactorsh`,
   `mapDerivedCategorySingleFunctor`, Ext exact-functor maps and LightCondensed facts.
   These supply machinery rather than this geometric comparison.
3. `msearch.py loogle`, query `Functor.mapDerivedCategoryFactors`: unknown unqualified
   identifier; query `CategoryTheory.Localization.liftNatIso`: three hits, namely
   liftNatIso and its hom/inv formulas. The latter is the generic construction used.
4. `msearch.py leansearch`, query "Inverse image from a condensed point commutes with
   scheme pullback on modules and unbounded derived categories": eight hits on
   `Scheme.Modules.pullback`, `SheafOfModules.pullback`, ordinary composition/congruence,
   stalk restriction and adjunction. None states the full node.
5. `msearch.py grep`, `pullbackComp|liftNatIso` under `Algebra/Homology/DerivedCategory`:
   no hits. Follow-up `mapDerivedCategory|liftNatIso` in the same subtree: ten hits
   including Mathlib ExactFunctor's actual construction and factorization.
6. Project `rg` for `upperStarFromPointModComp|upperStarFromPointMod` located the existing
   general ordinary construction in `WeilObject/Sheaf/Stalk.lean`, which is reused.
   Search for the exact item id in `lean/WeilConjectures` returned no hit.
   Searches in `lean/Sheaf` located private repeated ordinary constructions and the
   normed-field specialization `RootBoundary.pointPullComp` in ProfiniteDerivedEvaluation;
   none supplies this arbitrary-condensed-ring normalized derived statement. No private
   copy is imported or added. The new declaration names had no existing matches.

Validation: the new module compiled through the prescribed scompile.py server wrapper.
All variables and the single universe u are explicitly bound; autoImplicit is false.
All source lines are at most 100 characters. Only expected sorry warnings are allowed.
There is no STATEMENT-DISPUTED flag and no statement correction.

## Dependency modules

`def-weil-pbc-proetale-operations` receives a lean-only existing-interface repair under
brief-stage2 Section 1(B). Its old primary declaration, `proEtaleConstantRingDerivedPullback`,
is the arbitrary-constant-ring specialization; the node itself and the current consumer
need arbitrary commutative coefficient ring sheaves with the specified isomorphism c.
The original module already publicly reexports the general construction, so the repair
binds that exact existing general interface instead of adding any module or object:
`AlgebraicGeometry.Scheme.proEtaleRingDerivedPullback`, exported by
`Sheaf.AlgebraicGeometry.ProEtaleOperations` (its actual declaring module), together with
its module pullback/direct image, ordinary derived direct image, factorization and
module-operation properties. The normalized adjunctions remain exported by the already
existing ProEtaleOperationsCanonicalAdjunction, which the consumer imports. Their full signatures take `(f : X ⟶ Y)`, arbitrary `R` and `S` commutative
ring sheaves, and `(c : inverseImage(f).obj R ≅ S)`, exactly as this dependency states.
The statement and every other field of that dependency remain unchanged. Its Lean
signature in the record is copied verbatim from the source. This is an existing
binding repair, so no dependency Lean file is delivered or redefined.

Dry-run repair: the first preflight correctly required the primary existing declaration
to be attached to its actual declaring source file, not only a public reexport. The
dependency record now names ProEtaleOperations; its general signature and mathematical
content are unchanged. The consumer still imports the canonical-adjunction reexport.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
