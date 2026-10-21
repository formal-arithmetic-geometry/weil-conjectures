## Worker report

The module `Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization` states
`AlgebraicGeometry.ProEtale.CondensedRing.identity_open_derived_adjunction_normalization`.
Its only postponed proof is that theorem, with the six-step DAG proof in its docstring.
All five helper definitions have real data. The item node changes only in `lean`.
There are no new nodes, dependency repairs, or statement corrections.

Hypotheses and objects, matched to the node:

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- Field of positive characteristic p different from ell: `(k : Type u) [Field k]`,
  `(p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)`.
- Admissible commutative condensed coefficient: the module variables `Λ`, `[MonObj Λ]`,
  `[IsCommMonObj Λ]`, and `hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ`.
- Separated finite-type k-schemes: `U D Z : Scheme.{u}`, their `Over (Spec (.of k))`
  structures, and `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` on all three
  structure morphisms. Every map has its `IsOver (Spec (.of k))` instance.
- h:D→Z, quasi-compact open j, resulting open i, hi=j, and identity inverse-image locus:
  `(j : U ⟶ Z) (i : U ⟶ D) (h : D ⟶ Z)`, `[IsOpenImmersion j]`, `[QuasiCompact j]`,
  `[IsOpenImmersion i]`, `w : i ≫ h = j`, and `hw : h ⁻¹' Set.range j = Set.range i`.
  Open immersions are monomorphisms and identify their sources with the open image;
  these data express the specified isomorphism h⁻¹(U)≅U over U. No quasi-compactness
  assumption on i is added: it follows by base change of j.
- Small sites and internal modules: every module category is exactly
  `Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u+1}) (condensedRingObj Λ T)`.
  The site has object universe u+1 and morphism universe u, with coefficient universe u+1.
  The derived categories are the ordinary unbounded `DerivedCategory` of these categories.
- Specified pullbacks, direct images and adjunction: `upperStar`, `lowerStar`,
  `upperStarLowerStarAdjunction` from the upstream module-object framework. Their existing
  instances provide the stated additivity and exactness; no extra exactness hypothesis
  or auxiliary arbitrary functor is introduced.
- c_h is exactly the existing `identityOpenRestriction Λ j i h w`. The dependency theorem
  `identity_open_derived_restriction` identifies it sectionwise through
  `identityOpenSectionArrow` with the identity under the indicated fibre-product
  identification. Its existing normalization, not an independently chosen isomorphism,
  fixes the comparison used here.
- a_h is `identityOpenPullbackComparison`: `(upperStarComp Λ i h).symm` followed by
  `upperStarCongr Λ w`. With hi=j directly, the identity-on-U identification has already
  been removed by the functor unitor. `identityOpenDerivedPullbackComparison` is its
  termwise localization, using `mapDerivedCategoryCompIso` and `mapDerivedCategoryNatIso`.
- The precise adjunct hypothesis is `hc`: the adjunct is computed by
  `(upperStarLowerStarAdjunction Λ h).homEquiv M N t`; its j-pullback followed by c_h
  equals a_h inverse followed by i-pullback of t. Lean writes composition in diagram order.
- r_h is exactly `identityOpenDerivedRestriction Λ j i h w`, the recorded canonical map
  for (Z',j')=(D,i); its invertibility under these geometric hypotheses is already part
  of `identity_open_derived_restriction`, not an added assumption here.
- `identityOpenTermwiseDerivedAdjunction` is the actual
  `derivedUpperStarLowerStarAdjunction Λ h`, transported with `ofNatIsoLeft` along
  `leftDerivedUpperStarIsoMapDerivedCategory Λ h`. Its unit/counit therefore retain the
  specified adjunction normalization; no adjunction is chosen independently.

Conclusions, in their order in the Lean conjunction:

1. For every T and internal complex I, `I.IsKInjective ↔` K-injectivity of its image
   under `(InternalModuleOperations.equivalence Λ T).functor.mapHomologicalComplex`.
   This explicitly states preservation and reflection by the exact sectionwise equivalence.
   Preservation by its inverse follows by applying this equivalence and its unit/counit.
2. For every K-injective internal I on D, its termwise `upperStar Λ i` is K-injective.
   Through the recorded `upperComparison`, the previous equivalence identifies this
   with preservation under the sectionwise open restriction as well.
3. For every resolution `s : P ⟶ I` with `[QuasiIso s] [I.IsKInjective]`, the r-component
   followed by the exact localization identification equals j-pullback of the canonical
   evaluation `Rh_*(Qs) ≫ rightDerivedFunctorObjQIso I.hom`, followed by Q(c_I), followed
   by `inv (Q.map (C(i^*).map s))`. This is precisely the node's formula
   Q(i^*s)⁻¹ Q(c_I) j^*(d_s). There is no mono requirement on s.
   Every sectionwise K-injective resolution transfers to this formulation through the
   inverse exact equivalence; clauses 1--2 and the recorded operation comparisons ensure
   that the objects, quasi-isomorphism, and normalized sectionwise c are the same ones.
4. For every P (without a K-injective hypothesis), the comparison-unit identity is
   j's localization-factor inverse, j^*(gamma_P), r_QP, and i's localization-factor,
   equal to Q(c_P). Here gamma_P is the existing `rightDerivedFunctorUnitQ P`.
5. `Functor.IsRightDerivedFunctor` states the total right-derived universal property
   of `Rh_* ⋙ D(j^*)` with `identityOpenLocalizedDerivedUnit Λ j h`, relative to
   `HomologicalComplex.quasiIso`. Its source is exactly C(j^*)C(h_*) followed by Q.
   The helper inserts the same exact localization-factor inverse and the published
   unit, with functor associators. This class is Mathlib's left-Kan-extension formulation
   of the bijection of natural transformations in the definition node.
6. For every A on Z, `D(j^*)(eta_A) ≫ r_(h^*A) = a_A⁻¹`.
7. For every K on D, `D(i^*)(epsilon_K) = a_(Rh_*K) ≫ r_K`.
   Both use the units/counits of the specified transported adjunction. The maps on both
   sides come from natural transformations and natural isomorphisms, so these are
   natural equations in A and K, not choices of unrelated component morphisms.

Dependency declarations read and used (module prefixes are literal Lean module paths):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar`, `upperStar`,
  `upperStarLowerStarAdjunction`, `upperStarComp`; the latter is the specialization of
  Mathlib `CategoryTheory.Adjunction.leftAdjointCompIso` recorded on
  `def-sfb-module-upper-star-comp`, with its required inverse convention.
- The accompanying `UpperLowerStar.Coherence`: `upperStarCongr`, `upperStarId`.
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`:
  `AlgebraicGeometry.ProEtale.CondensedRing.module_pullback_additive_exact`.
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull` and its public upstream
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  `moduleObjectDerivedPushforward`, `moduleObjectDerivedPullback`,
  `derivedUpperStarLowerStarAdjunction`, `leftDerivedUpperStarIsoMapDerivedCategory`.
  The theorem uses the underlying general functors directly, which are the exact bodies
  of the first two abbreviating definitions; no derived construction is repeated.
- `Sheaf.Paper.IdentityOpenDerivedRestriction`: `identityOpenRestriction`,
  `identityOpenDerivedRestriction`, `identity_open_derived_restriction`,
  `identityOpenSectionArrow` (the canonical sectionwise interpretation).
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`:
  `AlgebraicGeometry.ProEtale.InternalModuleOperations.equivalence`, `ring`,
  `upperComparison`, and `internal_module_operations_transport`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: `CochainComplex.IsKInjective`;
  a resolution is a map with `QuasiIso` and this condition, exactly as its definition node.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` and its unit,
  universal property and resolution comparison; on the present Grothendieck categories
  the theorem uses the already published canonical `Functor.rightDerivedFunctor`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`:
  `CategoryTheory.Functor.rightDerivedFunctorObjQIso`;
  `...RightDerivedFunctor.ShortExactPullback`: `rightDerivedFunctorUnitQ` and its
  naturality. These definitions have been read, including their quotient/Qh transports.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`;
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `mapDerivedCategoryCompIso`, `mapDerivedCategoryNatIso`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `...Morphisms.FiniteType`: `LocallyOfFiniteType`; `...Morphisms.QuasiCompact`:
  `QuasiCompact` and `quasiCompact_isStableUnderBaseChange`.
- The setting node's recorded `compactificationOverField` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
  was read. Its setting is rendered by the explicit field/scheme/morphism binders above;
  this theorem uses neither a compactification nor bounded constructible objects, so
  that large downstream six-functor module is not imported just for its setting convention.
- Proof-only imports include the recorded `Adjunction.derived_adjoint_square_comparison`
  in `Sheaf.CategoryTheory.DerivedCategory.AdjointSquareComparison`,
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`
  in `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`,
  `Adjunction.preservesKInjectiveComplexes` in the upstream `RightDerivedFunctor.Comp`,
  open extension by zero and its adjunction from the upstream `LowerShriek.Defs`,
  and Mathlib localization universal-property interfaces. The other proof dependencies
  are already imported through the recorded restriction module or exact-functor modules.

Edge cases checked: U may be empty, j may be the identity, h may be the identity, and
h need not be proper or have dense identity locus. Zero complexes and the zero admissible
finite ring are allowed. The formula includes s=identity and arbitrary quasi-isomorphisms
s:P→I, and the unit identity includes non-K-injective P. There is no restriction to D⁺,
constructible objects, bounded complexes, or completed categories. No arbitrary non-open
pullback is asserted to preserve K-injectivity. The coefficient and site universes remain
the published ones, without equating site object and morphism universes.

Searches run through `msearch.py Q49 lem-sfb-identity-open-derived-adjunction-normalization`:

- LeanFinder, `K injective resolution normalization open restriction derived adjunction
  unit counit`: eight hits, mostly ordinary injective-resolution right-derived formulas
  and Scheme.Modules.restrictAdjunction_unit_app_app; no match for the pro-etale theorem.
- Loogle, `CategoryTheory.Adjunction.derived_unit`: one hit of that name; it is generic
  derived-adjunction infrastructure and does not state the identity-open normalization.
- grep, `rightDerivedFunctorUnit|derived_unit`, scope `CategoryTheory/Functor/Derived`:
  zero hits from that search service. Direct source inspection found the actual generic
  adjunction definitions; no absence conclusion rests on the service grep alone.
- LeanSearch, `unbounded derived direct image identity open restriction K injective
  normalization adjunction unit counit`: eight hits, including generic derived_unit,
  unit, and ordinary module sheaf restriction formulas; none is the full statement.
- `rg` of the item id and `identityOpen.*(Adjunction|Normalization)|identity_open_derived_adjunction`
  in both live `lean/WeilConjectures` and `lean/Sheaf` returned no existing match before
  writing. Focused `identityOpen|identity_open` searches found the prerequisite restriction
  module, which is reused. Focused right-derived-unit searches found the existing UnitQ,
  so the helper uses that rather than reconstructing the comparison component.

No statement dispute or source error was found. The source paragraphs read are
sites-cohomology.tex `lemma-restrict-direct-image-open` (0D6G) and
`lemma-restrict-K-injective-to-open` (08FI), and derived.tex
`lemma-derived-adjoint-functors` (09T5), together with the recorded compatible-square proof.

Validation: the prescribed scompile.py compiled both sandbox and library forms cleanly
(34.6 seconds and 37.1 seconds). Initial elaboration faults were field notation on an
unreduced HomologicalComplex and a line break inside field notation; explicit predicate
application fixed both, with no mathematical change. All variables/universes are bound
with `set_option autoImplicit false`; no line exceeds 100 characters.

## Second reading by Q49

This is a separate rereading by the same worker, not a claim of an independent agent review;
the dispatcher explicitly forbids starting other agents, and independent review belongs to
the maintainer. I reopened the node and compared its paragraphs to the seven conjuncts.
The main checks were orientation (Lean's compositions are diagrammatic), both localization
factorizations in the gamma equation, the inverse of Q(i^*s) at the end of the resolution
formula, and use of the actual transported derived unit/counit. The source formula
r_K composed with a_(Rh_*K) becomes a.hom.app (Rh_*K) followed by r.app K, exactly as
written. The adjunct hypothesis uses a.inv, also in the correct order. No additional
geometric hypothesis or arbitrary adjunction is present. The internal-resolution
formulation is the sectionwise formulation under the explicitly named exact equivalence
and its preserved/reflected K-injectivity, as explained clause by clause above.
