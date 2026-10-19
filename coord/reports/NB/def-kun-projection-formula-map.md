## Worker report

Item: `def-kun-projection-formula-map`. Attach the existing declaration
`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap` from
`WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`, lines 110–119.
No module is delivered: the existing definition already gives the stated construction.
Only the item's `lean` field changes. There are no new nodes, dependency repairs,
statement corrections, new proofs or new `sorry`s.

Sources read: the item's complete DAG record and all thirteen statement-dependency
records; their recorded source declarations and docstrings; the blueprint file
`sec-smooth-purity/sk-prop-sf-kunneth-ordinary/def-kun-projection-formula-map.md`
and its unit `_section.md`. Also read the existing projection-map module, its generic
adjunction construction, the derived adjunction construction, and the coefficient
instances. The existing upstream attachment is exactly the candidate already recorded
in the item, now checked by compilation rather than just source inspection.

### Hypotheses and clauses

All names in the following description are in `AlgebraicGeometry.Etale` unless qualified.
Specialize the upstream coefficient category `A` to `ModuleCat.{u + 1} Λ`.

1. **Schemes and arbitrary morphism.** The source binds `{X Y : Scheme.{u}}`
   and `(p : X ⟶ Y)`. Take `p = f`; no property of `f` is assumed.
2. **Commutative coefficient ring and size.** Use `(Λ : Type (u + 1)) [CommRing Λ]`.
   This is precisely the coefficient convention of the recorded derived-category
   dependency: `DerivedCategoryModule Λ T` abbreviates
   `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
   The site has scheme universe `u`, with module sheaves in the larger universe;
   schemes and rings may be lifted into a common bound as in the size convention.
   There is no restriction to a finite ring or a field.
3. **Exact constant-coefficient inverse image.** The underived functor is
   `upperStar (ModuleCat.{u + 1} Λ) f`, with right adjoint `lowerStar`.
   `leftDerivedUpperStarIsoMapDerivedCategory` identifies its total left derived
   functor with its exact termwise `mapDerivedCategory`. Thus the source's `Lf^*`
   denotes the node's `f⁻¹` through the canonical identification already recorded
   for `lem-kun-inverse-image-monoidal`; it introduces no different pullback notion.
4. **K-injective direct image and canonical derived adjunction.** The source uses
   `(lowerStar A f).rightDerivedFunctor` and `derivedUpperStarLowerStarAdjunction A f`.
   The latter is `(upperStarLowerStarAdjunction A f).derivedAdjunction`.
   In `CategoryTheory.DerivedCategory.Adjunction`, this is explicitly the localization
   of `adj.mapHomotopyCategory (.up ℤ)` with the left-derived counit and the
   K-injective right-derived unit. Thus its Hom bijection is induced by the termwise
   adjunction on K-injective representatives, as required, rather than a separately
   assumed adjunction. `preservesKInjectiveComplexes_lowerStar` is the specialization
   of `Adjunction.preservesKInjectiveComplexes` to the exact inverse image.
5. **Ordinary uncompleted derived tensor, including morphisms.** Every tensor in the
   existing construction is exactly `derivedTensor A T`, the declaration recorded
   by `def-kun-derived-tensor`. Its body is `curriedTensor _` on the K-flat-derived
   monoidal category; the complete functor acts in both variables. No completed
   tensor or degreewise Tor replaces it.
6. **Arbitrary E and K.** Evaluate the natural transformation as
   `((rightDerivedLowerStarProjectionMap A f).app E).app K`, where
   `E : DerivedCategory (Sheaf X.smallEtaleTopology A)` and
   `K : DerivedCategory (Sheaf Y.smallEtaleTopology A)`.
   These are the unbounded derived categories, without object-property subtypes.
7. **M and N and the direction of the resulting arrow.** The source bifunctors are
   `derivedTensorRightDerivedLowerStar A f` and
   `rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar A f`.
   Their two `obj_obj` equations in the same module expand to
   `Rf_*E ⊗ᴸ K` and `Rf_*(E ⊗ᴸ Lf^*K)` respectively. Consequently the component
   has exactly the displayed source `M` and target `Rf_*N`.
8. **The specified comparison c.** The morphism is
   `((leftDerivedUpperStarTensorComparison A f).app (Rf_*E)).app K`.
   `leftDerivedUpperStarTensorNatIso_hom` identifies this with the hom of the
   canonical natural isomorphism. The recorded monoidality node uses its inverse
   for the comparison `f⁻¹Rf_*E ⊗ᴸ f⁻¹K → f⁻¹(Rf_*E ⊗ᴸ K)`.
   Therefore the morphism used here has exactly the node's inverse direction.
   Its source construction derives the ordinary oplax tensor comparison; it is
   not an arbitrary selected isomorphism.
9. **The transpose α.** The right-hand side of
   `rightDerivedLowerStarProjectionMap_app_app` is `adj.homEquiv _ _` applied to
   the composite of that comparison with
   `((derivedTensor A X).map (adj.counit.app E)).app (Lf^*K)`.
   Functoriality in the first tensor variable makes this second arrow
   `ε_E ⊗ᴸ 1`, with the second variable fixed at `Lf^*K`.
10. **Explicit unit/direct-image composite.** The definition delegates to
    `CategoryTheory.Adjunction.rightAdjointProjectionMap`; its component is literally
    `adj.homEquiv _ _ α`. Mathlib's `Adjunction.homEquiv_unit` expands this to
    `adj.unit.app M ≫ Rf_*.map α`. This is exactly the node's explicit composite,
    including its chosen unit and counit.
11. **Equivalent adjoint description.** The existing theorem
    `homEquiv_symm_rightDerivedLowerStarProjectionMap` identifies the transpose
    of the component with precisely the composite in point 9.
12. **No extra geometric or homological assumptions, and no invertibility claim.**
    The source has coefficient-category structure instances, all available for every
    commutative `Λ`. `ModuleCat.hasFunctorialFlatResolution` supplies functorial flat
    resolutions, and importing
    `WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat` supplies
    `upperStarPreservesFlat_moduleCat`. Neither is an extra ring hypothesis.
    The output is a morphism/natural transformation, not an `Iso` or `IsIso` assertion.

### Dependency declarations read and used

The established six-functor encoding uses the following same notions. Since this delivery
attaches an existing declaration rather than adding a module, it introduces no additional
imports or copies of these dependencies.

| Dependency | Recorded module and declaration; role |
| --- | --- |
| `def-weil-size-convention` | Convention-only record; explicit `u`, `u + 1`, and the ambient derived-category universe implement the chosen size bound. |
| `def-weil-pbc-derived-categories` | `Sheaf.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`; its record identifies the category used here as `DerivedCategoryModule`, defined in `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`. The torsion predicate itself is not imposed. |
| `prop-weil-pbc-inverse-image-modules-exact` | `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`, `AlgebraicGeometry.etaleInverseImageModulesExact`; the ring/module transport package identifies constant-ring module pullback with exact inverse image and the abelian adjunction. The equivalent `ModuleCat Λ`-valued encoding used by the derived-category record is the upstream `upperStar`/`lowerStar`. |
| `lem-weil-pbc-exact-functor-derived-functor` | `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`, `CategoryTheory.Functor.exactFunctor_derivedFunctor`; exact termwise inverse image is its own derived functor. The upstream instance here is `leftDerivedUpperStarIsoMapDerivedCategory`. |
| `def-weil-pbc-kinjective-resolutions` | `Sheaf.AlgebraicGeometry.KInjectiveResolutions`, `CochainComplex.IsKInjectiveResolution`; quasi-isomorphism to a Mathlib `IsKInjective` complex. |
| `prop-weil-pbc-kinjective-resolutions-exist` | `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`, `CochainComplex.etale_kinjective_resolutions_exist`; the same unbounded sheaf category has K-injective replacements. |
| `lem-weil-pbc-kinjective-total-derived` | `Sheaf.CategoryTheory.KInjectiveTotalDerived`, `CategoryTheory.exists_rightDerived_of_enough_isKInjective`; universal total right-derived functor and its K-injective computation, implemented upstream by `Functor.rightDerivedFunctor`. |
| `lem-weil-pbc-termwise-adjunction-homotopy` | `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`, `CategoryTheory.Adjunction.mapHomotopyCategory`; used directly by the upstream derived adjunction construction. |
| `lem-weil-pbc-kinjective-hom-derived` | Mathlib `Algebra.Homology.DerivedCategory.KInjective`, `CochainComplex.IsKInjective.Qh_map_bijective`, with `quasiIso_iff`; the bounded-below clause is `DerivedCategory.Plus.Qh_map_bijective_of_isKInjective` in Mathlib `Algebra.Homology.DerivedCategory.Plus`. The unbounded Hom computation is the one relevant here. |
| `lem-weil-pbc-right-adjoint-preserves-kinjective` | `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`, `CategoryTheory.Adjunction.preservesKInjectiveComplexes`; supplies the direct-image K-injective preservation instance. |
| `def-kun-derived-tensor` | `WeilConjectures.SixFunctors.Etale.Derived.Tensor`, `AlgebraicGeometry.Etale.derivedTensor`; exactly the tensor used in both source bifunctors and the transpose. |
| `lem-weil-pbc-site-derived-tensor-descent` | `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`, `SheafOfModules.site_derived_tensor_descent`; the recorded general ringed-site presentation/descent statement. The upstream `derivedTensor` is already the registered constant-coefficient specialization, so no second tensor is selected from this existential theorem. |
| `lem-kun-inverse-image-monoidal` | `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`, `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorNatIso`, `leftDerivedUpperStarTensorComparison`, `isIso_leftDerivedUpperStarTensorComparison`, `leftDerivedUpperStarTensorIso`, and `leftDerivedUpperStarIsoMapDerivedCategory`; give exactly the canonical comparison and exact inverse-image identification used above. |

### Edge cases

The specialization was checked with completely arbitrary schemes, morphism, commutative
ring, and unbounded derived objects. The signature includes the empty scheme, the zero
ring, zero objects and complexes without any lower or upper cohomological bound.
The identity morphism is also permitted. No nonempty-site, nontrivial-ring, finite-ring,
properness, flatness-of-coefficients, finite Tor amplitude, or torsion assumption appears.
Flat resolutions and preservation of flat sheaves are global instances for every
commutative ring, not restrictions on `E` or `K`. A zero input gives the same well-typed
mate construction; no cancellation or inversion of the projection map is used.

### Searches actually run

The `msearch.py` log is in this sandbox's `searches.jsonl`.

- LeanFinder: `Projection formula morphism from derived direct image tensor K to derived
  direct image of E tensor inverse image K, defined as the adjunction mate of the tensor
  counit`. Eight hits, all `CategoryTheory.ExponentiableMorphism` results concerning
  slice-category pushforward; none is the derived étale construction.
- Loogle: `CategoryTheory.Adjunction, "projection"`. Zero hits.
- Mathlib grep: `rightAdjointProjectionMap|projectionFormula|projection.formula`, restricted
  to `CategoryTheory`. Zero hits.
- LeanSearch: `Projection formula map for unbounded derived categories of etale sheaves
  of modules defined by adjunction`. Service unavailable: `Internal Server Error`;
  recorded as unavailable, not as a negative search result.
- Source grep for `rightDerivedLowerStarProjectionMap` and projection terminology found
  the exact declaration and its two component/transpose formulas in
  `WeilConjectures/SixFunctors/Etale/Derived/LowerStarProjection.lean`.
- Source search for the item ID found no item-tagged implementation; the semantic/name
  search and the node's own `lean_candidates` identified the implementation instead.
- Project `lean/Sheaf` search for `ProjectionMap|projectionFormula|projection.formula`
  found general ringed-space/projection-formula work, not a duplicate of this exact
  étale derived component. `dag/lean_names_upstream.json` had no hit for the exact
  upstream declaration name. All matching upstream signatures and docstrings were read.

### Validation

`scompile.py NB def-kun-projection-formula-map scratchpad/ExistingProjectionCheck.lean`
compiled the arbitrary `ModuleCat.{u + 1} Λ` specialization, its `(E,K)` component,
component and transpose equations, monoidal comparison, exact inverse-image identification,
and derived adjunction. Local sandbox and published-library confirmation both succeeded
without warnings (2.2 and 2.3 seconds respectively).

`#print axioms AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap` reported only
`propext`, `Classical.choice`, `Quot.sound`. The module's old prose warning about `sorryAx`
through `derivedTensor` is stale: its current body is `curriedTensor _`, and the compiled
axiom output confirms this. There is no statement dispute or node fault.

The scratch check is outside `lean/` and is not a delivered module. The required delivery
dry run is the final validation; its outcome will be appended below.

Delivery dry run: `deliver2.py NB def-kun-projection-formula-map --no-push` printed
`OK (dry run)` for commit `2fd1e891d8`: the existing-declaration checks compiled and
preflight passed except for the independent second reading, which the second reader
must supply. Nothing was pushed. No second-reading section was written by this worker.


## Second reading by NB

Independent second reader, 2026-10-15. Verdict: the existing attachment says exactly
what this definition node says. No mathematical or Lean-record change is required.
This reading adds this report section and independent search/compile evidence only.

I read the sandbox node, its source blueprint definition and unit section, the thirteen
statement-dependency nodes, and the recorded declarations themselves. In particular I
opened `LowerStarProjection.lean`, `Adjunction/ProjectionMap.lean`,
`DerivedCategory/Adjunction.lean`, `Derived/UpperLowerStar.lean`,
`UpperStarMonoidal/Comparison.lean`, `Derived/Tensor.lean`, and
`Derived/Coefficients.lean` in the read-only upstream source. I also opened the dependency
modules for exact module inverse image, exact-functor derivation, K-injective resolutions,
existence and total right derivation, and site tensor descent, plus the recorded upstream
homotopy-adjunction and K-injective-preservation declarations and Mathlib's K-injective
Hom computation. There are no new nodes, dependency modules, or statement_change records
to review in this delivery.

Source check: Stacks `sites-cohomology.tex`, Section Projection formula, equation
`equation-projection-formula-map` (Tag 0B56), explicitly starts with an arbitrary morphism
of ringed topoi and arbitrary unbounded derived objects, "Without any further assumptions".
Its adjoint is pullback monoidality followed by the counit in the first tensor variable.
I also read `lemma-pullback-tensor-product` (07A4) and `lemma-adjoint` (07A6), including the
K-flat representative construction of the former. The properness, finite-type, separably
closed-field and invertibility hypotheses of the blueprint unit apply to its later
isomorphism assertions; they do not apply to this canonical-map definition.

### Node checklist and Lean correspondence

Below `A = ModuleCat.{u + 1} Λ`, `p = f`, and names without a namespace prefix are in
`AlgebraicGeometry.Etale`. This is a specialization and component evaluation of an existing
natural transformation, not an added general-coefficient assumption on the node.

1. **Objects X, Y and arbitrary f.** Upstream binds `{X Y : Scheme.{u}} (p : X ⟶ Y)`.
   No geometric class is required. Verdict: exact match.
2. **Commutative ring Λ and small-site size convention.** Specialize to
   `(Λ : Type (u + 1)) [CommRing Λ]` and `ModuleCat.{u + 1} Λ`. The categories are exactly
   `DerivedCategoryModule Λ X` and `DerivedCategoryModule Λ Y` in the recorded dependency,
   expanded as `DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
   The common universe bound is the dependency's explicit size convention, not a finite
   ring, field or characteristic restriction. Verdict: exact match.
3. **Exact constant-coefficient inverse image, left adjoint to direct image.** The
   construction uses `upperStar A f`, `lowerStar A f`, and their recorded abelian
   adjunction. `leftDerivedUpperStarIsoMapDerivedCategory A f` identifies its left-derived
   version with the exact termwise functor. The dependency module's transport along the
   canonical constant-ring comparison gives precisely this inverse-image notion; no
   structure-sheaf pullback is substituted. Verdict: match under the recorded canonical
   identification, as in the monoidality dependency.
4. **Rf_* computed with K-injective resolutions.** `lowerStar A f |>.rightDerivedFunctor`
   is the generic K-injective-derived functor, not a bounded-below derived functor.
   `IsKInjectiveResolution` is `QuasiIso f ∧ I.IsKInjective` on the same module-sheaf
   category. The recorded existence and total-derivation signatures give its replacements
   and computation. Verdict: exact match; no replacement is assumed as extra input.
5. **Canonical derived adjunction, unit and counit.**
   `derivedUpperStarLowerStarAdjunction A f` is
   `(upperStarLowerStarAdjunction A f).derivedAdjunction`. The latter is constructed
   from `adj.mapHomotopyCategory (.up ℤ)`, the K-flat left comparison and K-injective
   right comparison, by `Adjunction.derived`. Thus it derives the termwise adjunction;
   it is not an arbitrary adjunction on the two functors. Exact inverse image and
   `preservesKInjectiveComplexes_lowerStar` give the stated K-injective Hom computation.
   Its `.unit` and `.counit` are the η_f and ε_f used below. Verdict: match.
6. **Ordinary uncompleted derived tensor and its maps.** Both bifunctors and the
   transpose use the recorded `derivedTensor A T`, whose body is `curriedTensor _`
   for the K-flat-derived monoidal structure. This is the same ordinary tensor from
   `def-kun-derived-tensor`; it already acts on morphisms in both variables. The
   general site-descent dependency supplies the mathematical presentation, not a new
   existentially chosen tensor used here. Verdict: exact match.
7. **Arbitrary unbounded E and K.** The component is
   `((rightDerivedLowerStarProjectionMap A f).app E).app K`, with E in the entire
   derived category on X and K in the entire derived category on Y. Verdict: exact
   quantifiers, with no boundedness or object-property predicate.
8. **M, N and arrow source/target.** The two bifunctors
   `derivedTensorRightDerivedLowerStar` and
   `rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar` expand by their `obj_obj`
   equations to `Rf_* E ⊗ᴸ K` and `Rf_*(E ⊗ᴸ Lf^* K)`. Under item 3 these are precisely
   M and `Rf_* N`. Verdict: exact direction and tensor order.
9. **Specified inverse comparison c.**
   `((leftDerivedUpperStarTensorComparison A f).app (Rf_* E)).app K` goes from
   `Lf^*(Rf_* E ⊗ᴸ K)` to `Lf^* Rf_* E ⊗ᴸ Lf^* K`.
   `leftDerivedUpperStarTensorNatIso_hom` identifies it with the hom of the isomorphism
   recorded by `lem-kun-inverse-image-monoidal`; that node records the inverse for its
   oppositely directed display. The comparison derives the ordinary oplax structure,
   characterized by its representative square. Verdict: precisely c, not a chosen iso.
10. **α, the comparison followed by ε_E tensor identity.** The right-hand side of
    `rightDerivedLowerStarProjectionMap_app_app` uses c followed by
    `((derivedTensor A X).map (adj.counit.app E)).app (Lf^* K)`.
    Mapping in the first variable with the second fixed is exactly `ε_E ⊗ᴸ 1`.
    Lean's `≫` gives the same order as the node's displayed composite. Verdict: exact.
11. **Explicit composite η_M then Rf_*(α).** The definition calls
    `Adjunction.rightAdjointProjectionMap`; its component is literally
    `adj.homEquiv _ _ α`. Mathlib `Adjunction.homEquiv_unit` expands this as
    `adj.unit.app M ≫ (lowerStar A f).rightDerivedFunctor.map α`.
    Verdict: the stipulated explicit composite, with the same canonical unit.
12. **Equivalent adjoint description and no isomorphism assertion.**
    `homEquiv_symm_rightDerivedLowerStarProjectionMap` gives α as the transpose.
    The definition's type is `⟶` between bifunctors, not `≅` or an `IsIso` assertion.
    The coefficient-category structure arguments all have instances for every commutative
    Λ: notably `ModuleCat.hasFunctorialFlatResolution` and, with the recorded import,
    `upperStarPreservesFlat_moduleCat`. Verdict: no extra boundedness, properness,
    finiteness, flatness-of-inputs, or torsion hypothesis.

### Edge cases, searches, and mechanical checks

Empty schemes and the identity morphism are included by the unrestricted scheme and
morphism binders. Zero objects and unbounded complexes are included by the full derived
categories. The zero ring is permitted by `CommRing`; no `Nontrivial` instance occurs.
No index set, degree bound, or natural number n occurs here, so an empty index set and
n = 0 introduce no excluded case. All coefficient characteristics are covered. The
explicit universe u is bound; the coefficient successor universe and ambient derived
universe agree with the registered dependency and size convention. There is no extra
universe equality or auto-implicit variable.

Independent searches (logged in `searches.jsonl`):

- LeanFinder: "For an exact inverse image left adjoint to derived pushforward, the mixed
  tensor projection map is the mate of the counit tensored with identity". Eight hits,
  including monoidal-adjunction identities, tensor adjunctions, and
  `frobeniusMorphism_mate`. I opened the latter's source: it concerns Cartesian monoidal
  categories and the left-adjoint Frobenius map, not this right-derived module tensor map.
- Loogle: `"counit", "tensor"`. Twelve hits, principally monoidal-adjunction identities
  and equivalence/coalgebra formulas; none supplies this derived étale construction.
- Wrapper grep for `projectionMapTranspose|homEquiv_symm_rightDerivedLowerStar|rightAdjointProjectionMap`
  returned no Mathlib hits. Independent `rg` on upstream and project `lean/Sheaf` for
  `ProjectionMap|projectionMap|projection.formula|frobeniusMorphism` found the exact
  upstream map and its general adjunction construction. Other upstream projection maps
  concern compact support; project ringed-space constructions do not duplicate this
  registered constant-coefficient étale definition.
- LeanSearch: "The adjoint of pullback tensor comparison composed with the counit defines
  a projection formula morphism for derived sheaf direct image". Service unavailable
  (`Internal Server Error`); not treated as evidence of absence.

The sandbox `lean.statement` was compared programmatically with the source signature
from `noncomputable def` to `:=`; they are verbatim equal. The existing definition has
real data (the specified adjunction mate), not a hollow definition or a free map.
No new Lean module is delivered, so new-module docstring/proof requirements do not apply;
the upstream docstrings explicitly describe the same construction and transpose.
The node is a definition and has no proof steps. No theorem was added or proved.

I reran `scompile.py NB def-kun-projection-formula-map scratchpad/ExistingProjectionCheck.lean`
from the sandbox. Both sandbox-overlay compilation and published-library confirmation
passed without warnings, each in 2.2 seconds. The component, its transpose, canonical
comparison and exact inverse-image identification all elaborate for arbitrary Λ, f, E, K.
`#print axioms` again lists only `propext`, `Classical.choice`, `Quot.sound`.
No mismatch was found and no repair to the item was made.
