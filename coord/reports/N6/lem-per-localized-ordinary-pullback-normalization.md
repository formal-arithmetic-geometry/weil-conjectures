## Worker report

Delivered `Sheaf.Paper.LocalizedOrdinaryPullbackNormalization`, namespace
`AlgebraicGeometry.Scheme.LocalizedOrdinary`. The sole theorem is
`localizedOrdinaryPullbackNormalization`; its proof is `by sorry`. All helper
definitions contain real data; the four structures bundle the maps and equations
specified by this item, rather than assuming them. No new DAG notion or dependency
repair is needed. No change to the natural-language node is made.

### Hypotheses and objects

- Prime ℓ is `(l : ℕ) [Fact l.Prime]`. A finite extension is `(E : Type u)
  [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
- `PbcIntegralRing l E` is the existing ULift of O_E, with unchanged ring data.
  The arbitrary chosen `ϖ : PbcIntegralRing l E` and `_hϖ : Ideal.span {ϖ} =
  (pbcIntegralDatum l E).ideal` say precisely that ϖ generates the maximal ideal.
  This includes every uniformizer, not just `pbcUniformizer`. Thus the existing
  quotients by maximal-ideal powers are exactly A/(ϖ^(n+1)); the completed tower
  itself does not depend on the choice of generator. The ULift is only size transport.
- `X Y Z : Scheme.{u}`, `g : Y ⟶ X`, `h : Z ⟶ Y` are the three schemes and two
  maps; Lean's `h ≫ g` is the node's g∘h. Their hypotheses are the three
  `[IsNoetherian _]`, the three `[Fact (∃ n : ℕ, topologicalKrullDim _ ≤ n)]`,
  and the three stalkwise `[Fact (∀ x, IsUnit (l : _.presheaf.stalk x))]`.
- `ProEt.topology` and `proEtaleSheafInverseImage` are the actual small sites and
  inverse images. Site objects have universe u+1, morphisms u, coefficient rings
  u+1. No equality between site object and morphism universes is imposed.
- `B` aliases `pbcAdicCompletion`; its projections are `pbcAdicProjection`.
  `completedFiniteCoefficientMap` is the actual constant-section map d; and
  `completedCoefficientMap` is the actual limit-cone map c, not an arbitrary map.
  The positive exponent n is represented by Lean n-1 (index 0 means exponent 1).
- `uniformizer` is the compatible constant scalar section for the chosen ϖ.
  `R` is `ringedLocalizationRingOfUniverses` of B at that section, and `iota`
  is its actual unit. These definitions temporarily disable an ambiguous sheafify
  instance only inside those commands; they do not alter the exported instance set.
- `pbcModules` and `DerivedCategory` are the existing module and ordinary unbounded
  derived categories. P is `pbcActualModulePull` / `pbcActualDerivedPull`; these
  use the arbitrary completed coefficient morphism, without an invertibility premise.
  `F₀` and `F` are ordinary/derived `pbcExtend` along iota. `G₀` and `G` are pure
  inverse image (over the actual inverse-image ring, hence a reflexive identification)
  followed by ordinary/derived scalar extension along the localized coefficient map.
  The reflexive identification is only for pure inverse image; c and d^E are never
  required to be invertible.

### Every conclusion and normalization

- `Coefficients.finite_comp` states finite-level composition, with the canonical
  `proEtaleRingInverseImageComp` included explicitly. `completed_comp` does the
  same for c. `projection_comp` is the double-pullback projection equality in the
  display; composing `completed_comp` with the final projection supplies its other
  equality, including the canonical compositor.
- `Coefficients.transitions` states commutation with every quotient transition
  q in ℕᵒᵖ. `finite_id` and `completed_id` are the canonical inverse-image identity
  isomorphism on coefficients. `scalar` fixes every integral constant section,
  in particular the arbitrary ϖ. Its projections give the finite scalar assertion.
- `Edge.coefficient_unit` is the localization-unit square for d^E; localization's
  universal property uniquely determines it, including the local fraction formula
  c(b)/ϖ^r. `Composition.coefficient_comp` and `Identity.coefficient_id` retain
  its composition and identity normalization. Thus there is no independent choice
  of the localization/inverse-image comparison.
- `Edge.ordinary` and `Edge.derived` are δ before and after deriving.
  `ordinary_tensor` is balanced flattening: e⊗(b⊗m) becomes e·iota(b) times
  the tensor-unit section. `ordinary_unit` retains the unit case explicitly;
  `ordinary_inverse_unit` gives unit insertion by the inverse. Module linearity
  and local fraction generation determine the arbitrary rational coefficient case.
- `Composition.ordinary_tensor` is precisely b(e''⊗e'⊗m) =
  e''·d_h^E(e')⊗m, with `scalarSection` displaying the coefficient map after
  the inverse-image adjunction unit. `ordinary_inverse_unit` states insertion
  of 1 for b inverse. Chart transports use `MorphismProperty.Over.pullbackComp`.
- `Composition.ordinary_square` equates the two ordinary paths, using the inverse
  of `pbcActualModulePullCompIso` because that published isomorphism is oriented
  P_comp → P_g ⋙ P_h. `ordinary_mixed_tensor` gives their explicit common value
  e''·iota(c_h(b'))⊗m, after absorbing the intermediate B_Z coefficient. The first
  path is written in that field and the second is equal to it by `ordinary_square`.
  This is stated for every module, hence in particular each term of a flat-term
  K-flat complex, with `m` its degreewise element.
- `Edge.derived_model`, `Composition.derived_model`, and `Identity.derived_model`
  fix the derived comparisons through the actual computation counits on every
  flat-term K-flat cochain complex. The K-flat predicate is the recorded
  `CochainComplex.IsKFlatIndependentCoefficients`, with explicit universe witnesses;
  flat terms use `SheafOfModules.IsFlatOnSite`. `counit` is the actual composite of
  exact inverse-image computation and scalar-extension computation counits.
- `Composition.derived_square` states the displayed δ_comp F(a) =
  b G_h(δ_g) δ_h equation for every `K : PbcCompletedDerived X ...`.
  Despite this type alias's name, it is the whole ordinary derived category,
  with no completeness condition or constructibility restriction on K.
- `Identity.ordinary_tensor` states scalar multiplication into the module.
  `Identity.ordinary_square` and `derived_square` are e_E δ_id = F(e), using
  the canonical `pbcActualModulePullIdIso` / `pbcActualDerivedPullIdIso`.
- All ordinary comparisons are natural isomorphisms of sheaf functors, so their
  components commute with restrictions and are natural in modules. Applying
  `NatIso.mapHomologicalComplex` makes them chain maps, thus commuting with
  differentials. The derived comparisons are natural isomorphisms of functors on
  the entire unbounded derived category, thus natural for every derived morphism.
  The representative equations specify those same chain maps, not a separate
  existential isomorphism lacking a normalization.
- The theorem's conjunction asserts the coefficient identities and existence of
  all these normalized comparison data for g, h, h≫g, and id_X. It does not add
  any assumption about coefficient-map invertibility or flatness.

### Dependency declarations

The recorded declarations were read along with their full signatures/docstrings.
The actual lower-level coefficient and pullback declarations reexported by those
modules are used, rather than copies of the notions.

- `def-pc-kflat-complex`: `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`, `CochainComplex.IsKFlatIndependentCoefficients`. Additional recorded declarations are used through its public imports.
- `def-pur-sheaf-tensor-product`: `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, `SheafOfModules.cochainModulesMonoidal`. Additional recorded declarations are used through its public imports.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`. Additional recorded declarations are used through its public imports.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-pbc-adic-coefficient-datum`: `Sheaf.Paper.AdicCoefficientDatum`, `AlgebraicGeometry.Scheme.completedReductionTower`. Additional recorded declarations are used through its public imports.
- `def-weil-pbc-completed-pullback`: `Sheaf.Paper.PbcQbarCompletedPullback`, `AlgebraicGeometry.Scheme.pbcQbarCompletedPull`. Additional recorded declarations are used through its public imports.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-pbc-ringed-section-localization`: `Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses`, `CategoryTheory.ringedLocalizationRingOfUniverses`. Additional recorded declarations are used through its public imports.
- `def-weil-proetale-inverse-image`: `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`. Additional recorded declarations are used through its public imports.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `lem-sfb-ringed-derived-monoidal-comparisons`: `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`, `CategoryTheory.RingedDerivedComparisons.ringedDerivedMonoidalComparisons`. Additional recorded declarations are used through its public imports.
- `lem-weil-pbc-localization-inverse-image-coherence`: `Sheaf.CategoryTheory.LocalizationInverseImageCoherence`, `CategoryTheory.existsUnique_localizationInverseImage`. Additional recorded declarations are used through its public imports.
- `lem-weil-pbc-site-morphism-composition`: `WeilConjectures.CategoryTheory.SiteMorphismComposition`, `CategoryTheory.siteMorphism_composition`.

In particular, `Sheaf.Paper.PbcQbarCompletedPullback` publicly exports
`CompletedTowerPullback`'s `completedFiniteCoefficientMap` and
`completedCoefficientMap`, plus the actual all-module pullback of
`PbcCompletedPullbackActual`. `Sheaf.Paper.PbcActualRingedExchange` supplies the
canonical `pbcActualModulePullCompIso`, `pbcActualDerivedPullCompIso`, and their
identity versions, all retaining their ordinary unit/counit normalization.
`Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition` supplies the canonical
`proEtaleRingModuleUnitSection`; it is used only with the identity identification
on the inverse-image ring. `integralUnitSection` is a typed alias of the existing
integral tensor-unit section on its base-changed chart.

### Edge cases

Checked identity maps and their chart isomorphisms: all fields reduce to scalar
multiplication and unit insertion. Empty source schemes and the zero complex
introduce no nonempty assumptions. The first quotient is index 0, exponent 1;
there is no accidental exponent-zero quotient. All integers are allowed as complex
degrees and K is arbitrary, so no bounded-below restriction appears. Torsion
modules, including ϖ-torsion ones killed by localization, remain admitted.
No field/domain hypothesis is put on section rings; zero localizations are admitted.
Noninvertible c_u and d_u^E are scalar-extension inputs, not isomorphisms.
Every chosen uniformizer generating the maximal ideal is included.
No disputed statement or node correction was found.

### Searches

- LeanFinder via msearch.py: “Derived pullback of module sheaves commutes with
  localization of coefficient rings compatibly with composition and identity”.
  Eight hits, headed by `SheafOfModules.pullbackComp`, `pullback_assoc`, and the
  identity coherences. They concern ordinary pullback, not this entire normalized
  completed-coefficient/derived-localization statement.
- Loogle via msearch.py: `"pullbackComp"`. Twelve hits, headed by
  `CategoryTheory.Limits.pullbackComparison`; no match.
- Mathlib grep via msearch.py: `pullbackComp|extendScalarsComp`. Twenty-five hits;
  read the ordinary module sheaf pullback/scalar extension interfaces. They supply
  basic comparisons but do not state this normalization theorem.
- LeanSearch via msearch.py: “Derived localization of coefficient sheaves commutes
  with ringed pullback and composition”. Eight hits including
  `SheafOfModules.conjugateEquiv_pullbackComp_inv`, `SheafOfModules.pullbackComp`,
  `SheafOfModules.pullback_assoc` and scheme structure-sheaf pullback; no full match.
- rg of WeilConjectures and Sheaf for completed coefficient, localized pullback,
  rational realization, and composition, plus grep for the exact item identifier:
  no exact existing declaration. Read `RationalPullbackCompositionCoherence` and
  `RationalRealizationPullbackComparison` completely. Their stronger constructible
  realization interfaces are not hypotheses of this ordinary all-module statement.
  `CompletedCoefficientRingedCoherence` supplies coefficient composition but not
  the localization comparison or derived tensor normalization clauses.

### Validation

All compiles use the prescribed scompile.py server wrapper. The final module
compiles both as the isolated sandbox module and at its library path. The only
postponed proof is the main named theorem; all variables/universes are explicitly
bound and `autoImplicit` is disabled. The node's `lean.statement` is extracted
verbatim from the theorem keyword through the signature before `:=`.

## Second reading by N6

Performed a separate clause-by-clause rereading of the node and completed module
in this session. The dispatcher explicitly forbids starting other agents, so this
is a self-review and does not claim to be an independent second worker's reading.
The maintainer's independent review remains necessary under the supplied brief.
The reading found and repaired three potential losses of precision: the originally
fixed library uniformizer was replaced by an arbitrary generator ϖ of the same
maximal ideal; the common mixed-tensor value was added explicitly; and ordinary
inverse unit insertion was added explicitly. Rechecked every hypothesis and clause
against the mapping above. Site universes remain u+1/u, and all K are unbounded
objects of the full ordinary derived category. No extra RationalModuleRealization,
constructibility, flatness-of-coefficient-map, or invertibility premise was added.
