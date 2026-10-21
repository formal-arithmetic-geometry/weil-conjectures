## Worker report

The module `Sheaf.Paper.PullbackIdentitiesScalarExtension` states both clauses of
`lem-pod-pullback-identities-scalar-extension` as the conjunction in
`WeilConjectures.pullbackIdentities_scalarExtension`. Its proof is `sorry`.
The node's mathematical statement, dependencies, and proof are unchanged.

Hypotheses and the objects they determine:

- The explicit universe `u`, `(l : ℕ) [Fact l.Prime]`, fields `E`, `L`, their
  `Algebra ℚ_[l]` and `FiniteDimensional ℚ_[l]` instances give the prime and two
  finite coefficient extensions. `ι : E →ₐ[ℚ_[l]] L` gives the inclusion. A field
  algebra homomorphism is injective; thus this is the coordinate-free presentation
  of the stated subextension in an algebraic closure. No choice of ambient closure
  appears in either formula, and identity inclusions are allowed.
- `sfIntegralConstructibleCategory l E W` is exactly the recorded full category of
  complete objects with constructible reductions and one common finite interval.
  There is no perfection, finite Tor-amplitude, or extra boundedness hypothesis.
- `integralScalarExtensionOfUniverses l E L ι W` is the recorded scalar extension,
  definitionally the same resolving-class localization as the equal-universe
  `integralScalarExtension` used by the realization formulas. Both have the same
  completed coefficient sheaf and actual strict Roos construction.
- `constructibleIntegralPullback` is the recorded restriction of
  `integralDerivedPullback`. Thus its object's `.obj` is the ambient pullback
  literally, and no replacement functor or object is introduced.
- `D : IntegralComparisonSystem.{u} l` supplies the simultaneously normalized
  whole-system realization data of the specified dependency. Its coefficient
  models retain their universal representative normalization; this is not a tuple
  of arbitrary comparison isomorphisms. Both clauses use
  `integralComparisonScalar ... D`, and clause 1 uses
  `integralComparisonComposition ... D`. These are the displayed lambda/mu and
  eta formulas of the realization module. Quantifying over its normalized
  realization data makes the statement independent of their presentation choices.
  No coefficient-change or pullback comparison is an independent parameter.
- In each clause the schemes are arbitrary `Scheme.{u}` with instances
  `∀ x, Invertible (l : X.residueField x)`, precisely invertibility of l on them.
  The small pro-etale sites retain object universe `u+1` and morphism universe `u`.
  No finite type, separatedness, nonemptiness, or finite-field assumption occurs.

Clause 1:

- `h : Z ⟶ W`, `k : W ⟶ V`, and
  `K : sfIntegralConstructibleCategory l E V` render every stated input.
- Lean composition `h ≫ k` is the scheme morphism k composed with h.
- The left side is, in Lean's left-to-right composition order,
  `T_Z.map (c_E ...).hom ≫ alpha_h(Lk_E K).hom ≫ Lh_L.map alpha_k.hom`.
  This is exactly the three factors in the displayed composition identity.
- The right side is `alpha_(h ≫ k).hom ≫ c_L(T_V K).hom`, with scalar extension
  on the full subcategory expressed by `integralComparisonConstructibleScalar`.
  Its underlying object is the same ambient scalar extension. All endpoints are
  therefore the node's endpoints, without casts or unrelated identifications.

Clause 2:

- `g : X ⟶ Y` with `[IsIso g]` renders an arbitrary scheme isomorphism, and
  `inv g` renders its inverse. `K` ranges over every stated integral constructible
  object on Y.
- `inverseImageIntegralDerived` is the already recorded exact sectionwise
  inverse image with the completed coefficient action transported by the
  quotient-projection-normalized coefficient map.
- `pullbackIdentitySiteUnit` is the actual site identification
  `𝟭 Y.ProEt ≅ Phi_(inv g) ⋙ Phi_g`, obtained from `Over.mapId` at
  `inv g ≫ g = 𝟙 Y` and `Over.mapComp`. Its arrows have identity underlying
  scheme maps. It is fixed by formulas, with no choice of site equivalence.
- The auxiliary theorem `pullbackIdentityModuleCounit_existsUnique` supplies the
  uniquely determined natural module isomorphism whose every section map is
  `M.val.map ((pullbackIdentitySiteUnit g).hom.app U).op`. This is exactly the
  canonical inverse-image identification in the definition of epsilon. The
  theorem records its linearity and uniqueness, with a full proof plan in its
  docstring. `pullbackIdentityModuleCounit` selects from this unique specification;
  this is not selection of arbitrary data from mere existence.
- `pullbackIdentityInverseImageCounit` applies that actual module counit termwise
  and localizes, with the canonical exact-functor composition and identity
  comparisons. Thus the last arrow of epsilon is fixed on representatives.
- `pullbackIdentityKappa_isIso` records the invertibility assertion explicitly
  included in the node's setup, specialized to its intrinsic complete category.
  Its proof plan applies the recorded normalization theorem to the recorded
  canonical coefficient calculus. Its only proof is `sorry`.
- `pullbackIdentityLambda` is literally
  `(asIso (inverseImagePullbackComparisonDerived ... K.obj)).symm`, using that
  invertibility. In particular the old unnormalized existential lambda of the
  isomorphism-pullback lemma is not silently selected.
- `pullbackIdentityEpsilon` is, in order, lambda for inv g at Lg K, the inverse
  image under inv g of lambda for g at K, then the counit just described. This
  is exactly the node's definition, including normalization by kappa inverse.
  Its stalk-unit proofs are derived from the residue-field invertibility
  instances by the local residue map. They are not extra theorem assumptions.
- The second conjunct is
  `alpha_(inv g)(Lg_E K).hom ≫ L(inv g)_L.map alpha_g.hom ≫ epsilon_L(T_Y K).hom
   = T_Y.map epsilon_E(K).hom`, exactly the displayed inverse identity.
  Equality of these homs is equality of the isomorphisms, since `Iso.hom` is
  injective. The full constructible categories are full subcategories, so ambient
  equality of their arrows expresses the same equality.

All definitions have real data. The two auxiliary postponed theorems are the
existence/linearity/uniqueness of the canonical counit and the explicitly stated
invertibility of kappa needed to define clause 2. They are helpers belonging to
this node's own inverse-identity setup, not new independent notions or copies of
existing declarations. Each is recorded in `lean.declarations`, carries this
node's blueprint tag, and has a source and complete natural-language proof plan.

Dependency interfaces read and used (module and declarations):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; its public coefficient constructions
  supply the valuation rings, uniformizers and positive quotient rings.
- `def-weil-scheme-morphism-properties` is a convention record: the scheme and
  invertibility hypotheses use Mathlib's `Scheme`, residue fields and
  `Invertible`; it has no module/declaration of its own.
- `Sheaf.Paper.SfIntegralConstructible`:
  `WeilConjectures.sfIntegralConstructible`, `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`:
  `WeilConjectures.integralScalarExtensionOfUniverses`.
- `Sheaf.Paper.DerivedPullbackTensorHom`:
  `WeilConjectures.constructibleIntegralPullback`; its underlying
  `integralDerivedPullback` is from `Sheaf.Paper.IntegralDerivedOperations`.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`:
  `WeilConjectures.scalarPullbackCompleted`, the tensor/completion construction
  of the scalar comparisons; this dependency is publicly imported, while the
  node explicitly selects its whole-system-normalized form below.
- `Sheaf.Paper.IntegralPullbackComposition`:
  `WeilConjectures.IntegralPullbackCompositionFamily`,
  `integralPullbackComposition`; the selected canonical family is its specified
  whole-system realization rather than an arbitrary existential witness.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage`, and the recorded site
  construction used by the sectionwise model.
- `Sheaf.Paper.IsomorphismDerivedPullback`:
  `WeilConjectures.isomorphismIntegralDerivedPullback_termwise`, for the
  preservation and natural comparison assertions of the inverse-identity setup.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `AlgebraicGeometry.Scheme.isoSectionwiseInverseImage`,
  `isoSectionwiseModuleInverseImage`, their equivalence/exactness interfaces,
  and the publicly retained `proEtaleIsoPostcompose`.
- `Sheaf.Paper.IntegralPullbackComparisonRealization`:
  `IntegralComparisonSystem`, `integralComparisonComposition`,
  `integralComparisonScalar`, `integralComparisonConstructibleScalar`,
  `IntegralComparisonRealizationCoherence`,
  `integralPullbackComparisonRealization`, all in `WeilConjectures`.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`:
  `AlgebraicGeometry.ProEtale.inverseImagePullbackComparisonDerived`, with its
  exact derived-object signature and chosen representative/K-flat formula.
- `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization`:
  `WeilConjectures.isomorphismDerivedPullbackComparisonNormalization`.
- Proof imports are `Sheaf.Paper.IsomorphismComparisonScalarExtension`
  (`isomorphismComparisonScalarAlpha`, `isomorphismComparisonScalarBeta`,
  `isomorphismComparison_scalarExtension`) and
  `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
  (`completedScalarComparison`, `finiteFreeCompletedScalarComparison`).
  `lem-pod-isomorphism-scalar-comparison-agreement` has no recorded Lean
  declaration, so no module for that unstated proof dependency is imported.

Edge cases checked: E=L with the identity inclusion; g the identity; either h
or k the identity; zero K; empty schemes; arbitrary characteristic in which l
is a unit; arbitrary bounded intervals including shifted and non-perfect inputs.
The site unit includes its actual `inv_hom_id` transport, so the identity and
inverse cases do not depend on definitional equality of scheme composites.
No exclusion is introduced for any of these cases. The typechecker verifies all
intermediate objects and both composition directions. Nothing asserts kappa is
invertible on incomplete ambient objects.

Searches performed with the prescribed `msearch.py` (full search log is in the
sandbox `searches.jsonl`):

- LeanFinder: “Derived complete integral pro etale pullback composition and inverse
  identities commute with finite scalar extension” returned eight hits concerning
  affine scheme pullbacks and etale algebra maps, not this statement.
- Loogle: `PresheafOfModules.pullbackComp` returned that definition and its
  associativity/identity lemmas. They concern ordinary presheaf pullback and do
  not state completed integral scalar coherence.
- Grep: `pullbackComp|extendScalars` in `Algebra/Category/ModuleCat` returned 25
  ordinary module/sheaf/presheaf scalar and pullback declarations; none is the
  stated completed derived identity.
- LeanSearch: “Scalar extension commutes with composition of derived pullbacks
  and inverse image equivalence counit” returned eight ordinary module extension
  and tensor-associativity declarations; none gives these normalized maps.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the node id, the proposed
  declaration names, scalar/pullback identities and inverse-image counits found
  the existing realization formulas and general comparison modules described
  above, but no theorem combining these two clauses and no existing counit for
  this completed sectionwise inverse-image functor. The existing
  `IntegralInverseImageComparisonComposition` supplies the compositor, not the
  inverse-image counit used here. No existing declaration is restated.

The source proof was read in the current `main-20261015` snapshot. Its pullback
identity and inverse automorphism pasting are rendered with precisely the
normalizations supplied by this DAG node. No statement fault or dispute found.

Validation: prescribed `scompile.py` compiled both the sandbox module and its
library module successfully (19.9 s and 22.6 s), without errors or warnings.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
