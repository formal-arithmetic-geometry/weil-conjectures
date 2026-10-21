## Worker report

Item: `lem-sfb-module-derived-compositor-coherence`, NH, stage 2.
Module: `Sheaf.Paper.ModuleDerivedCompositorCoherence`.
The node's natural-language statement, statement dependencies, proof and proof dependencies
are unchanged. Only its `lean` record is changed. No new or repaired dependency nodes are
needed. The declaration list records three canonical helper isomorphisms and four theorem
statements, all belonging to clauses of this item. Every new theorem has exactly `sorry`
as its proof; the helper definitions have real data from the existing derived-functor API.

Source read: the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-prop-sf-comp-coherence/det-sf-comp-coherence-cocycle.proof.md`,
"Refinement isomorphisms", in particular the identification
`Rp_* Rh_* = R(ph)_*` and the identity/transitivity claims. Also read Stacks
`sites-cohomology.tex`, Tag 0D6E, `lemma-derived-pushforward-composition`, lines 4010–4030.
The node isolates the normalized structural coherence underlying those claims.

Hypothesis and clause correspondence:

- A commutative condensed coefficient ring is the section variable
  `Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}` with `[MonObj Λ]`
  and `[IsCommMonObj Λ]`. Each theorem has `(ℓ : ℕ) [Fact ℓ.Prime]` and
  `(hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)`, using the recorded admissibility
  predicate without copying its list of coefficient rings.
- The pulled-back coefficient on any scheme is exactly `condensedRingObj Λ T`, the
  unbundled object of the recorded `coefficientRing T (Mon.mk Λ)` construction.
  There is no arbitrary replacement ring, action or coefficient comparison.
- The module category is Mathlib's `CategoryTheory.Mod` in the abelian-sheaf category
  of the actual small pro-etale site `Scheme.ProEt.topology T`. Its ordinary unbounded
  derived category is `DerivedCategory`; no bounded-below, constructible, complete or
  localizing subcategory occurs. The existing Grothendieck-category instances supply
  derived categories and K-injective resolutions. Universes follow the published
  framework: schemes in `u`, site objects in `u + 1`, site morphisms in `u`, abelian
  coefficients in `u + 1`, and the induced module/derived categories. There is no
  imposed equality between object and morphism universes.
- Arbitrary maps `X → Y → Z → W` are `{X Y Z W : Scheme.{u}}` and
  `(f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)`. No geometric hypotheses are present.
- The specified module direct image is the recorded `CondensedRing.lowerStar Λ f`.
  Its coefficient identifications and ordinary compositor are exactly the existing
  `lowerStarComp Λ f g`; its inverse image and adjunction are the recorded `upperStar`
  and `upperStarLowerStarAdjunction`. No private notion of direct image is introduced.
- `moduleDerivedCompositor Λ f g` has direction
  `R(lowerStar Λ (f ≫ g)) ≅ R(lowerStar Λ f) ⋙ R(lowerStar Λ g)`.
  It specializes `Functor.rightDerivedFunctorCompIso'` to the actual ordinary
  `lowerStarComp`, and takes the inverse. The K-injective-preservation instance is
  supplied inside the definition by the existing exact-left-adjoint criterion applied
  to `upperStarLowerStarAdjunction Λ f`; preservation is not an added hypothesis.
  The generic comparison is characterized by the resolution-unit equation, so under
  `sectionModuleEquivalence` it is the comparison of
  `ringedToposDerivedPushforwardComposition`. That theorem's uniqueness clause makes
  this identification canonical; no choice of an unspecified isomorphism is used.
- The K-injective normalization is
  `module_derived_compositor_normalization`. For every actual module complex `I` with
  `[I.IsKInjective]`, its left side is the compositor at `DerivedCategory.Q.obj I`
  followed by the successive standard resolution identifications. Its right side is
  the standard resolution identification for the composite pushforward followed by
  `Q.mapIso` of the inverse of `mapHomologicalComplexCompIso (lowerStarComp Λ f g)`
  at `I`. This explicitly states the inverse termwise compositor, with its original
  module action. `moduleDerivedIteratedObjIso` uses `rightDerivedFunctorObjQIso` first
  for `f` and then for `g`, using the actual K-injective complex `f_* I`.
- The primary declaration `module_derived_compositor_coherence` is the displayed
  associativity equation. The left path is `κ_(h,gf)` followed by `Rh_* κ_(g,f)`;
  in Lean's covariant functor-composition notation this is
  `moduleDerivedCompositor Λ (f ≫ g) h` followed by `isoWhiskerRight` of
  `moduleDerivedCompositor Λ f g`. The right path is transport of the source along
  `Category.assoc f g h`, then `moduleDerivedCompositor Λ f (g ≫ h)`, then
  `isoWhiskerLeft Rf_* (moduleDerivedCompositor Λ g h)`.
  `Functor.associator` on the left puts both codomains in `Rf_* ⋙ (Rg_* ⋙ Rh_*)`.
  Equality of natural isomorphisms states equality of their natural transformations
  (the inverse components are determined).
- `moduleDerivedIdentity Λ T` is derived from the actual `lowerStarId Λ T`, followed
  by the existing exact-functor comparison `R(Id) ≅ D(Id)` and
  `Functor.mapDerivedCategoryIdIso`. `module_derived_identity_normalization` explicitly
  identifies its component on every K-injective `I` with the termwise `lowerStarId`
  followed by `mapHomologicalComplexIdIso`. Thus its source is the sectionwise identity
  direct image specified in the node, rather than an arbitrary identity comparison.
- `module_derived_compositor_units` has both clauses as a conjunction. Composing
  `κ_(f,1_X)` with `isoWhiskerRight ε_X Rf_*` and `leftUnitor` equals the canonical
  transport along `Category.id_comp f`. Composing `κ_(1_Y,f)` with
  `isoWhiskerLeft Rf_* ε_Y` and `rightUnitor` equals transport along
  `Category.comp_id f`. Equivalently both constraints are identities after precisely
  those equality identifications. Neither identity case is discarded.

Dependency declarations read and used:

- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`,
  `condensedRingObj`, `isCommMonObj_condensedRingObj` and
  `condensedPushforwardHom_comp`. The basic module is publicly imported by the
  module-pushforward framework.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, their
  action axioms and module morphisms, supplied by the framework imports.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`,
  `preservesHomology_upperStar` and `lowerStarComp`, with their full signatures and
  docstrings. The derived upper/lower-star module imports this public interface.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions` and its resolution-unit/uniqueness
  interface. The node's derived-category convention permits the canonical upstream
  `Functor.rightDerivedFunctor` on these Grothendieck module categories; this is used
  directly rather than introducing a second derived functor.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence` (including its
  site/coefficient universes and its definition from the section-module functor).
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `CategoryTheory.ringedToposDerivedPushforwardComposition`, including the unit equation,
  uniqueness and K-injective-resolution normalization. Imported for the proof route.
- Proof interfaces imported: `Sheaf.CategoryTheory.RingedDerivedCompositionCocycle`
  (`ringedDerivedComposition_cocycle`, `ringedDerivedComposition_units`),
  `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`, and
  `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`.
  `Adjunction.preservesKInjectiveComplexes` is the existing declaration from
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp` and is used
  as real data in the helper definitions. The two proof dependencies
  `lem-sfb-section-ring-lax-pushforward-coherence` and
  `lem-pd-section-derived-pushpull-normalization` have no recorded Lean module in the
  read snapshot; their DAG proof plan is retained in the docstrings. They are not
  assumptions or redefinitions in this delivery.
- Additional existing constructions: `Functor.rightDerivedFunctorCompIso'`,
  `rightDerivedFunctorNatIso`, `rightDerivedFunctorObjQIso`,
  `rightDerivedFunctorIsoMapDerivedCategory`, `mapDerivedCategoryIdIso`,
  `mapHomologicalComplexCompIso`, `NatIso.mapHomologicalComplex`,
  `mapHomologicalComplexIdIso`, and the ordinary `lowerStarId`/`lowerStarCongr`.

Edge cases checked before writing: identity on either side (both laws are explicit),
all three maps identities (associator and scheme associativity still inserted), the
zero complex (K-injective, both normalized maps reduce to the ordinary zero-object
isomorphism), the empty scheme, and the zero/finite coefficient ring. Non-flat finite
coefficients are allowed: the argument uses exact inverse image from the point, not
flatness of the coefficient ring. No nonempty, proper, dense, finite-type, Noetherian,
field, boundedness or derived-completeness assumption is hidden in the signature.
No disputed statement or node correction was found.

Searches actually run (2026-10-21):

1. `msearch.py ... leanfinder` with query "Canonical composition isomorphisms for
   unbounded derived direct images of condensed module sheaves satisfy associativity
   and identity normalization": eight hits, including `SheafOfModules.pushforward_assoc`,
   `SheafOfModules.pushforwardComp` and ordinary sheaf/presheaf composition comparisons.
   None states the normalized unbounded module-object theorem.
2. `msearch.py ... loogle` with query
   `CategoryTheory.Functor.rightDerivedFunctorCompIso, CategoryTheory.Functor.rightDerivedFunctorCompIso_assoc`:
   zero hits; the service does not index the upstream `rightDerivedFunctorCompIso`
   identifier. Local reading did find that generic upstream constructor; it is reused.
3. `msearch.py ... grep` query `rightDerivedFunctorCompIso|rightDerivedFunctorIdIso`
   in Mathlib `CategoryTheory`: zero hits.
4. `msearch.py ... leansearch` query "Canonical composition and unit isomorphisms of
   unbounded derived pushforward functors of module objects satisfy associativity":
   eight hits, including `SheafOfModules.pushforward_assoc` and ordinary pushforward
   comparisons; no exact theorem with the module-object derived normalization.
5. Direct `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` for
   `rightDerivedLowerStarComp`, `derivedLowerStarComp`, `lowerStar.*[Cc]ompositor`,
   `module_derived_compositor`, and candidate declaration names. The exact upstream
   compositor/coherence matches are for finite-coefficient sheaf categories; the
   module-object framework has derived upper-star coherence but no corresponding
   lower-star compositor. The generic derived-composition theorem exists and is used.
   `grep -rn 'lem-sfb-module-derived-compositor-coherence' lean/WeilConjectures` found
   no declaration. Searches of `dag/lean_names_upstream.json` and both source roots
   found none of the new declaration names. Existing generic functors and module
   constructions are imported rather than copied.

Validation uses only the prescribed `scompile.py`/`deliver2.py` wrappers. The first
compile diagnosed a module-category notation/scope ambiguity; the module now uses
fully qualified `CategoryTheory.Mod` and the published `CategoryTheory.Obj` scope.
The next compile diagnosed the explicit category argument of
`Functor.mapHomologicalComplexIdIso`; that argument is now supplied. No mathematical
hypothesis or conclusion changed in either repair.

Final validation: `scompile.py` compiled the sandbox and named library module cleanly
in 25.8 s and 32.2 s respectively. `deliver2.py --no-push` returned
`OK (dry run): commit 35ad57809e7 passes the preflight and compiles; nothing pushed`.

## Second reading by NH

This is the writing worker's second reading, not a claimed independent agent review;
the dispatch brief forbids spawning agents and assigns independent review to the maintainer.
I reopened the node and final module and checked each clause above against its type.
In particular, the compositor points from the composite pushforward to the iterated
pushforward, the normalization uses the inverse ordinary compositor, the associativity
source is explicitly transported from `(f ≫ g) ≫ h` to `f ≫ (g ≫ h)`, and the two unit
clauses use the identity comparison on different sides. The identity normalization
has the final termwise-identity identification, so its endpoint is the actual complex
`I`. All four named theorem statements retain the identical admissibility hypotheses.
The three helper definitions use existing canonical constructions with no `sorry` data.
Only the two elaboration repairs described above were needed; no statement mismatch
or missing edge case was found.
