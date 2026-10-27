## Worker report

Item: `lem-sfb-identity-open-module-sections`. The new module
`Sheaf.AlgebraicGeometry.IdentityOpenModuleSections` states
`AlgebraicGeometry.ProEtale.CondensedRing.IdentityOpenModuleSections.identityOpenModuleSections`.
The one theorem has proof `sorry`; its docstring gives all six DAG proof steps.
Seven transparent predicates/type families only unpack this single node's clauses.
There are no new independent notions, new nodes, dependency repairs, or statement changes.
The sandbox node differs from the repository node only in `lean`.

The sources read were Stacks `sites-cohomology.tex`,
`lemma-restrict-direct-image-open` (0D6G), particularly its underived equality and its
citation of `sites-modules.tex`, `lemma-localize-morphism-ringed-sites` (04J0).
The latter explicitly states `f'_* j_U^* = j_V^* f_*` for localized ringed sites.
The node correctly applies this underived part, not the derived assertion of 0D6G.
The inverse-pair calculation is the fibre-product universal property of 01JO.
No source or statement defect was found.

### Hypotheses and clauses

All names below are in the module namespace
`AlgebraicGeometry.ProEtale.CondensedRing.IdentityOpenModuleSections` unless qualified.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Any commutative condensed ring Λ | `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `[MonObj Λ] [IsCommMonObj Λ]`. This is exactly the underlying object plus monoid structure of the dependency's `Profinite.CondensedRing = Mon (...)`, with commutativity; it does not require a topological presentation, admissibility, or a finite/discrete ring. |
| Every scheme, small sites in the common coefficient universe | Every scheme binder is `Scheme.{u}`, every test object is `U.ProEt`, and the abelian coefficient category is `Ab.{u + 1}`. The site is Mathlib's `Scheme.ProEt`, with its existing topology. No independent smaller coefficient or test-object universe is imposed. |
| Λ_T = p_T^* Λ and the module category | `condensedRingObj Λ T` is the existing pulled-back ring object, and modules are `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)`. |
| Specified module direct/inverse images and coefficient comparisons | All functors are the existing `CondensedRing.lowerStar Λ h`, `upperStar Λ j`, etc. `ModuleOpenPasting.coprojection` uses their specified module adjunction units. `ModuleOpenPasting.inverseImageActionIso` is extension along the actual `condensedPullbackHom` identified with comap along its inverse. No map or functor is supplied as an extra hypothesis. |
| j and j' are open immersions | Explicit `(j : U ⟶ Z) (j' : U ⟶ Z')` and `[IsOpenImmersion j] [IsOpenImmersion j']`. |
| h j' = j | Explicit `(h : Z' ⟶ Z)` and `w : j' ≫ h = j`. Lean composition is diagrammatic. |
| h inverse-image(j(U)) = j'(U) as open subschemes | `hw : h ⁻¹' Set.range j = Set.range j'`. For open immersions, an open subscheme is determined by its underlying open subset, so this is exactly the node's condition, as in its parent's existing statement. |
| For every v:V→U, projection π is an isomorphism | `ProjectionGeometry` gives `e V : pullback (V.hom ≫ j) h ≅ V.left` with `(e V).hom = pullback.fst ...`. Thus it states invertibility of the actual chosen projection, not merely an unrelated isomorphism of schemes. |
| Its inverse is (1_V,j'v) | The inverse's first projection is `𝟙 V.left` and its second is `V.hom ≫ j'`. The universal property uniquely characterizes the pair, without a second copy of the parent module's `identityOpenSectionArrow` constructor. |
| Inverses natural in V | The last clause of `ProjectionGeometry` quantifies over `t : V ⟶ W` and equates `t.left ≫ (e W).inv` with `(e V).inv` followed by the map of base changes of `objectComposition j`. This is the requested naturality square. |
| Open pullback is sectionwise restriction for j and j' | `OpenRestriction Λ` quantifies over every open immersion j, every module M and every `V : U.ProEt`. It asserts bijectivity of the specified `ModuleOpenPasting.coprojection Λ j M V`, whose domain is exactly `M(V→U→Z)`. The same universally quantified assertion applies to j'. These are canonical identifications, not a literal equality between scalar extension and its input. |
| The action is transported through α_j inverse | The second clause of `OpenRestriction` uses the specific `ModuleOpenPasting.inverseImageActionIso Λ j`. It equates its image of each module coprojection with the abelian-sheaf coprojection given by the abelian adjunction unit followed by the site graph restriction. The target of that existing isomorphism is `mapMod(j^*_Ab) ⋙ Mod.comap (inv (condensedPullbackHom Λ j))`. Thus the section coordinates and the inverse-scalar action are explicitly linked, not just separately asserted to exist. |
| Existence of natural module isomorphisms c_h | `∃ c : Comparisons Λ, ...`, where `Comparisons` quantifies over precisely the commuting common-open diagrams and has value `lowerStar Λ h ⋙ upperStar Λ j ≅ upperStar Λ j'`. Components are module isomorphisms, their maps are linear for the specified actions, naturality in modules is part of a natural isomorphism, and naturality in V is part of its underlying sheaf morphisms. |
| Section map is M(π inverse), hence identity after π | `Normalized` says the comparison sends `coprojection Λ j (h_* M) V s` to `coprojection Λ j' M V (M.X.obj.map a.op s)`. Here `a` is written directly with `Over.homMk (pullback.lift (𝟙 V.left) (V.hom ≫ j') ...) ...`. It is exactly the inverse pair of `ProjectionGeometry`, as an arrow of the pro-etale site over Z'. The oppositely directed sheaf restriction therefore has exactly the node's domain and codomain. |
| Uniqueness of the natural module isomorphism | `UniqueNormalized` first asserts `Normalized` for the selected comparison and then states that every natural module isomorphism `d` with that section formula equals it. This is pointwise uniqueness for every diagram, not just uniqueness among already coherent families. |
| Additional open j'' and k, with the same conditions | `Composition` binds `j'' : U ⟶ Z''`, `[IsOpenImmersion j'']`, `k : Z'' ⟶ Z'`, `w' : j'' ≫ k = j'`, and `hw' : k ⁻¹' Set.range j' = Set.range j''`, in addition to all h-diagram data. |
| c_hk = c_k ∘ (c_h k_*) ∘ (j^* μ_h,k inverse) | The right side of `Composition` is `whiskerRight (lowerStarComp Λ k h).inv (upperStar Λ j)`, followed by the functor associator, then `whiskerLeft (lowerStar Λ k) (c ... h ...).hom`, then `(c ... k ...).hom`. This has source `(hk)_* ⋙ j^*` and target `j''^*`. It is precisely the node's inverse-compositor order. The left side uses `k ≫ h`; the proofs of its commutativity and preimage-open condition are explicit terms made from w,w',hw,hw', not extra assumptions. |
| Identity h=1_Z and j'=j | `Identity` evaluates c at `(𝟙 Z)`, `Category.comp_id j`, and `rfl` for the range condition. Its hom equals `whiskerRight (lowerStarId Λ Z).hom (upperStar Λ j)` followed by `Functor.leftUnitor`. Thus it is identity under the specified canonical identity-pushforward comparison. |
| All associators/fibre-product identifications | The composition associator is written out. Projection naturality uses the existing pullback functor on actual site objects. Section arrows are actual lifts to the chosen pullback; the module compositor already incorporates the canonical iterated-pullback identification. |
| No additional geometric or derived assumptions | There are no properness, density, field, quasi-compactness, prime, admissibility, boundedness, or derived-category binders or conclusions. |

### Dependency declarations read and used

- `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing`,
  `Profinite.CondensedRing`; its transparent `Mon` abbreviation explains the unbundled ring binder.
- `sk-def-sfb-pulled-back-coefficients`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`, `condensedRingObj`,
  and `isCommMonObj_condensedRingObj`. These construct the point-pullback ring and its structure.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod`, `ModObj`, and module morphisms with the action compatibility.
- `sk-def-sfb-module-pushforward-pullback`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
  `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar`, `upperStar`,
  `upperStarLowerStarAdjunction`, `lowerStarComp`, and `upperStarComp`.
  The defining formulas, underlying sheaf/action statements and adjunction were read.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt` and `ProEt.topology`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion` (the scheme locally-ringed-space condition).
- `def-sfb-module-lower-star-comp`: the same upstream Defs module's `lowerStarComp`.
  Its inverse, not its hom, is used in the displayed composition law.
- Canonical identity comparison:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence`,
  `AlgebraicGeometry.ProEtale.CondensedRing.lowerStarId`.
- The already-stated proof dependency `lem-sfb-module-direct-image-open-pasting`:
  `Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting`,
  `ModuleOpenPasting.coprojection`, `inverseImageActionIso`, and
  `moduleDirectImageOpenPasting`. The first two canonical constructions are used directly
  in the statement; the theorem supplies the proof plan, particularly Sectionwise and
  MixedPasting. Its definitions and entire statement/docstring were read.
- Other stated proof dependencies are imported explicitly or transitively:
  `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`, `Scheme.ProEt.weaklyEtale_localization`;
  `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison`, `Scheme.proEtale_ringed_open_comparison`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`, `SheafOfModules.overFunctor`;
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`, `Mod.extendScalars`,
  `Mod.comap`, `Mod.extendScalarsIsoComapInv`;
  `Mathlib.CategoryTheory.Adjunction.CompositionIso`, `Adjunction.leftAdjointCompIso`;
  the upstream abelian-sheaf `lowerStar` and generic `Limits.pullback`/projections/lift.
  No statement dependency was found to have an unusable recorded interface.

### Edge cases and scope checks

- Empty U and empty schemes are admitted: no nonemptiness, density, or inhabited-section
  condition is present. All section claims quantify over every actual site object.
- Identity h is included without an extra premise: the commuting equality is
  `Category.comp_id j`, and the preimage equality is definitional `rfl`.
- When U=Z and j is identity, the preimage condition forces the other open to cover
  Z'; the geometric assertion then correctly says h is inverse to j'.
- No restriction is placed on h outside the common open; extra components away from it
  are allowed. Omitting the preimage condition would admit extra fibres over U, so
  it is retained in `Comparisons`, `ProjectionGeometry`, uniqueness and composition.
- Zero modules and arbitrary nonconstant condensed coefficients remain included.
  Neither a constant coefficient ring nor a localizing-admissible hypothesis is substituted.
- Composition is checked in Lean's diagrammatic order k then h: the functors start at
  modules on Z'', and the specified compositor inverse has exactly the necessary source.
- No auto-implicit variables, local notation, local instances, or hidden `let` binders
  occur. The coefficient and site universes follow the existing upstream convention.

### Searches for an existing statement

Searches used the prescribed `msearch.py Q92 lem-sfb-identity-open-module-sections` wrapper.

- `leanfinder`: “Restriction of module sheaf direct image to an open where a scheme
  morphism is the identity gives a unique sectionwise normalized natural isomorphism
  compatible with composition”. Eight hits, including
  `Scheme.Modules.restrictFunctorId`, `restrictFunctorAdjCounitIso`,
  `restrictFunctorComp_hom_app_app`, and restriction naturality formulas.
  These are Zariski structure-sheaf module statements, not this pro-etale condensed-module
  statement with arbitrary coefficients and the required section normalization.
- `loogle`: `SheafOfModules.pushforwardId, SheafOfModules.pushforwardComp`.
  Two hits: `SheafOfModules.pushforward_id_comp` and `pushforward_comp_id`.
  These are generic pushforward unit laws, not the common-open comparison.
- `grep` in Mathlib `AlgebraicGeometry/Modules`:
  `pushforwardId|pushforwardComp|restrictFunctorComp`.
  Ten hits in `Modules/Sheaf.lean` and `Modules/Tilde.lean`; these give the same generic
  or Zariski module constructions, not this theorem.
- `leansearch`: “For pro etale module sheaves over arbitrary condensed coefficients
  an identity over a common open gives a unique sectionwise direct image restriction
  isomorphism with identity and composition laws”. Eight hits, including
  `SheafOfModules.pushforwardComp_hom_app_val_app`, `Scheme.Modules.restrict_obj`,
  `restrictFunctorAdjCounitIso`, and `restrictFunctorCongr` variants.
  No exact match.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf`:
  `identityOpen|IdentityOpen|identity.open.module|lem-sfb-identity-open-module-sections`.
  The relevant existing file was `Sheaf/Paper/IdentityOpenDerivedRestriction.lean`.
  Its underived assertion is bundled with derived claims and requires a prime,
  `IsLocalizingAdmissibleCoefficient`, and quasi-compact open immersions. It therefore
  cannot serve as this unrestricted node's statement. Its canonical arrow was read;
  the new statement writes the universal-property expression directly rather than
  declaring a duplicate arrow or importing the downstream parent.
  The underived square-normalization theorem was also inspected and has additional
  admissibility/quasi-compactness hypotheses and extra normalization clauses.
- The exact item-id search in `lean/WeilConjectures` found no declaration.
  Searches for `identityOpenModuleSections|IdentityOpenModuleSections|ProjectionGeometry`
  in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found no
  collision. The general `ModuleDirectImageOpenPasting` result is reused as above.

### Validation

The delivered file compiled cleanly through `scompile.py` as both a sandbox module and
`Sheaf.AlgebraicGeometry.IdentityOpenModuleSections`. After strengthening the explicit
inverse-action coordinate clause, it was compiled again: both checks passed (6.8 s and
6.3 s). No warning other than the permitted postponed theorem proof was reported.
The declaration record contains the exact verbatim theorem signature and all seven
helper declarations. Line lengths were checked against 100 characters.

The dispatched brief forbids starting other agents. No independent worker reading is
claimed here; the maintainer's independent delivery review remains the independent check.

## Second reading by Q92

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
