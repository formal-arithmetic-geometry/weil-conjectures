## Worker report

The module `Sheaf.Paper.IntegralLocalizationHomColimit` states
`AlgebraicGeometry.ProEtale.CondensedRing.integralLocalization_hom_colimit`.
Its sole theorem has proof `sorry`; it introduces no definitions or helper theorems.
The node is unchanged except for its `lean` record. No statement correction,
new node, or dependency repair is necessary.

Hypotheses and conclusions, matched to the node:

- A prime ℓ is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- A finite normed extension E/ℚ_ℓ is `(E : Type) [NormedField E]
  [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]`, exactly the coefficient
  convention of the recorded dependency.
- A scheme X with Noetherian underlying topological space is `(X : Scheme.{u})
  [TopologicalSpace.NoetherianSpace X]`. This does not assert a stronger scheme
  finiteness condition.
- Integral bounded constructible K and B are `(K B : integralConstructible ℓ E X)`.
  The existing abbreviation is the full subcategory
  `ProEtale.BoundedConstructible (condensedRingObj (integralCoeff ℓ E) X)`;
  its objects are bounded in the canonical t-structure and have constructible
  cohomology in every degree. `K.obj` and `B.obj` are the corresponding objects
  of the actual ordinary derived category. There is no derived completeness
  hypothesis or replacement by discrete coefficients.
- The diagram in the first conjunct is the diagram of
  `integralLocalizationCocone ℓ E X B.obj`. The definition uses
  `integralLocalizationSequence ℓ B.obj = Functor.ofSequence (fun _ ↦ ℓ • 𝟙 B.obj)`.
  Thus every stage is B and each successive transition is multiplication by ℓ.
- The cocone's vertex is exactly U(L(B)), for
  `Mod.derivedExtendMapDerivedCategoryAdjunction
  (coefficientMap (integralScalarMap ℓ E) X)`. Its left adjoint is the existing
  `integralScalarExtension ℓ E X`; its right adjoint is derived restriction of
  scalars. The definition's nth leg is `adj.unit.app B.obj ≫ U.map (t ^ n)`,
  where `t = inv (ℓ • 𝟙 (L.obj B.obj))`. The nth inverse power is inverse
  multiplication by ℓⁿ, so these are precisely the specified legs.
- Every integer target shift is `∀ q : ℤ` in the first conjunct. The functor
  `shiftFunctor _ q ⋙ preadditiveCoyoneda.obj (op K.obj)` takes T to the
  additive Hom group Hom(K,T[q]). Its mapped cocone has nth leg postcomposition
  with the shifted localization leg. `colimit.desc _` of that mapped cocone
  is the canonical map from the abelian-group colimit; `IsIso` asserts exactly
  that this map is an isomorphism of abelian groups.
- The second conjunct is the recorded `homColimitProperty`, applied to
  `integralLocalizationLiftedSequence.{u + 2, u + 1, u + 1} ℓ B.obj` and
  `integralLocalizationLiftedCocone.{u, u + 1} ℓ E X B.obj`, at K.obj.
  Unfolding the property gives the same shifted comparison for every integer.
  These two existing definitions reindex the same diagram and cocone along
  `(ULift.orderIso : ULift.{u + 1} ℕ ≃o ℕ).equivalence.functor`.
  This is the lifted indexing universe used by the shared coefficient framework.
  The ordinary ℕ clause is written directly because the shared
  `homColimitProperty` ties the index universe to the category's Hom universe;
  the direct expression is literally its defining comparison, with ordinary ℕ.
  No equality between site object and morphism universes is imposed.
- Neither conjunct assumes that the scalar diagram has a colimit in the derived
  category. Only the colimit in abelian groups occurs in the signature.

Dependency declarations read and used:

- `Sheaf.Paper.ContinuousIntegralCoefficients`:
  `AlgebraicGeometry.ProEtale.CondensedRing.integralCoeff`,
  `integralConstructible`, `integralScalarMap`, `integralScalarExtension`.
  Its upstream definition is `AlgebraicGeometry.ProEtale.boundedConstructible`
  / `BoundedConstructible` in
  `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`.
- `Sheaf.Paper.ContinuousIntegralLocalization`:
  `AlgebraicGeometry.ProEtale.CondensedRing.integralLocalizationSequence`,
  `scalarLocalizationUnitCocone`, `integralLocalizationCocone`,
  `integralLocalizationLiftedSequence`, `integralLocalizationLiftedCocone`.
- `Sheaf.CategoryTheory.HomColimitExtension`:
  `CategoryTheory.homColimitProperty` and, for the proof plan,
  `CategoryTheory.homColimitProperty_extensions`.
- Proof-only imports retain every recorded proof dependency:
  `DerivedCategory.bounded_cohomology_cone_witness` in
  `Sheaf.CategoryTheory.DerivedCategory.BoundedCohomologyConeWitness`;
  `integralComplexLocalization_colimit` in
  `Sheaf.Paper.ContinuousIntegralComplexTelescope`;
  `integralConstructible_sheaf_hom_colimit` in
  `Sheaf.Paper.IntegralConstructibleSheafHom`;
  `localizationCocone_isColimit_of_model` in
  `Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport`;
  `exists_integralLocalization_complex_model` in
  `Sheaf.Paper.ContinuousIntegralLocalizationModel`;
  and Mathlib's `CategoryTheory.Pretriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.
  All five coefficient-layer theorem names in this bullet have namespace
  `AlgebraicGeometry.ProEtale.CondensedRing`.

The theorem docstring carries all six proof steps of the DAG: strict complex
scalar colimit and good truncation; AsSmall reindexing and constructible sheaf
continuity; closure under zero, isomorphisms and shifts; finite cohomology cone
induction with triangle rotation and extension closure; transport from the strict
model of B; and all-leg identification and ULift reindexing.

Source checked: the supplied Bhatt–Scholze PDF, Lemma 6.8.12 and Proposition
6.8.14(2). The lemma asserts RHom/direct-sum continuity on the bounded-below
part, and the proposition uses it for full faithfulness after inverting ℓ.
The node's scalar-telescope specialization and proof agree with that application.

Edge cases checked before drafting: K=0, B=0 and acyclic objects make the
comparison a map between zero groups; no nonzero-object hypothesis was added.
The empty scheme is allowed. Arbitrarily negative shifts q are included, as are
complexes with negative cohomological bounds and integral ℓ-torsion. No common
bound for K and B is imposed. The prime hypothesis excludes ℓ=0 and ℓ=1 exactly
as the node does. ℕ and ULift ℕ retain stage zero and every subsequent stage.
`Scheme.{u}` leaves the scheme universe arbitrary and the Hom groups live in the
existing coefficient framework's universe u+1.

Searches actually run:

- `msearch.py ... leanfinder` with query “Shifted Hom from bounded constructible
  integral pro etale complexes commutes with the scalar localization unit
  telescope”: eight hits on `LocalizerMorphism.smallShiftedHomMap_mk` /
  `_comp`, shift compatibility, homology sequences, and
  `DerivedCategory.left_fac_of_isStrictlyLE_of_isStrictlyGE`; none states this
  coefficient-specific Hom-colimit isomorphism.
- `msearch.py ... loogle` with query `"IsColimit", "preadditiveCoyoneda"`:
  zero hits.
- `msearch.py ... grep` with query
  `integralLocalization|homColimitProperty|constructible.*telescope`:
  zero Mathlib hits.
- `rg -n` with the same pattern in the upstream `lean/WeilConjectures` and
  project `lean/Sheaf`: the upstream search gives no match; the project search
  finds the recorded telescope definitions and generic/sheaf-source continuity
  inputs, homology continuity, and `IntegralConstructibleSequentialHom`.
  The latter only asserts finite-stage factorization, so it is not the full
  group isomorphism here. `ConstructibleHomContinuityDevissage` treats a generic
  continuity locus and does not state this specified localization comparison.
- `grep -rn` for the item id in upstream `lean/WeilConjectures`: no matches.
- `rg -n integralLocalization_hom_colimit` in upstream sources, project sources,
  Mathlib and `dag/lean_names_upstream.json`: no existing declaration by this name.

Validation: `scompile.py NY lem-sfb-integral-localization-hom-colimit` compiled
both its sandbox probe and its library module cleanly (3.0 s and 2.9 s).
`autoImplicit` is explicitly false. No declaration is claimed proved.
No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
