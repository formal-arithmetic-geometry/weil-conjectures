## Worker report

The module `Sheaf.Paper.EffectiveComparisonRealizationModels` states
`WeilConjectures.effectiveComparisonRealizationModels`, with `sorry` as its only
postponed proof. It asserts `Nonempty (EffectiveComparisonRealizationModels l)`.
The structure packages precisely the simultaneous witnesses and asserted properties;
it constructs no unknown object by choice. The Prop-valued helper
`IsEffectiveComparisonCompletionNormalized` spells out the initial strict quotient
augmentation. No new DAG nodes, dependency repairs, or statement corrections are needed.

Clause-by-clause reading:

- Prime ell: `(l : ℕ) [Fact l.Prime]` in the theorem and structure.
- Finite coefficient extensions: the `E`, `L : Type u`, `Field`, `Algebra ℚ_[l]`,
  and `FiniteDimensional ℚ_[l]` binders. `ι : E →ₐ[ℚ_[l]] L` is a coefficient
  inclusion (automatically injective for fields). All embeddings are quantified
  simultaneously. In particular any fixed-algebraic-closure chain E→L→M, its
  composite, and all equalities of fields occur in the very same witnesses.
  Abstract field models express these inclusions without choosing a new closure.
- Schemes and scheme maps: `X Y : Scheme.{u}`, `f : X ⟶ Y`. Every scheme binder
  carries `[∀ x : X, Invertible (l : X.residueField x)]`, the usual statement
  that ell is invertible. No properness, Noetherian, or finite-type condition occurs.
- Valuation rings, positive quotients, completed sheaves and small pro-etale sites
  are the existing dependency constructions inside `CoefficientDerivedSystemCalculus`,
  `coefficientSequenceModules`, `scalarReductionSource`, and the primitive model types.
  Lean level `n : ℕ` is the positive quotient n+1, not quotient by the zeroth power.
- The whole-system reduction/realization adjunction is `system E X`, whose
  `reduction` and `adjunction` use precisely `coefficientSequenceLimit` as right
  adjoint. Its objects are derived objects of the actual ringed sequence site,
  retaining quotient-linear transitions, rather than arbitrary diagrams of derived
  objects. The system scalar and pullback functors are the recorded
  `integralComparisonDerivedSequenceScalar` and `integralComparisonDerivedSequencePullback`.
- Simultaneous Roos models are `roos E X : IntegralComparisonRoosModel l E X`.
  This contains a natural comparison on *entire tower complexes*, and `computes`
  fixes it on every K-injective tower by the actual ordinary-limit cone.
  `integralComparisonLimitToRoos` has the ordinary limit tuple in its unshifted
  coordinate and zero in its shifted coordinate, by its defining unique property.
- The first displayed primitive isomorphism is `(pullback E f).realization`.
  Its `normalization` is the published `IsIntegralComparisonPullbackNormalized`,
  quantifying over every flat-term K-flat representative and every simultaneous
  quotient presentation, with actual quotient transitions and inverse-image generators.
- The second displayed primitive isomorphism is `(scalar E L ι X).realization`.
  Its `normalization` is `IsIntegralComparisonScalarNormalized`, using the same
  reduction diagram, the actual universal cochain change-of-rings counit and
  multiplication on tensor generators. Thus simultaneous reassociation is fixed:
  `(x tensor a) tensor b` maps to `x tensor ab`; the whole-system associator
  `integralComparisonSequenceScalarComposition` has the corresponding actual
  scalar multiplication formula, and commutes with every quotient transition.
  These are properties of the imported interfaces, not unrelated chosen isomorphisms.
- Initial completion normalization: `completion_normalization` applies
  `IsEffectiveComparisonCompletionNormalized` to the chosen `system` and `roos`.
  Its `v` is an actual chain map from P to the Roos complex of the restriction
  of its *whole* quotient presentation C. The first conjunct specifies every
  unshifted projection, on every degree and every site section, as the actual
  `unrestrictedIntegralTensorSection ... 1 x`, transported along κ inverse.
  The second conjunct says `v.f i ≫ mappingCocone.snd.v i j h = 0`.
  The third identifies `DerivedCategory.Q.map v` with the actual adjunction unit
  followed by the presentation and the chosen Roos bridge. For any P→K this is
  precisely the node's formula after transport by the inverse representative
  isomorphism, using naturality of the adjunction unit. It is an equality of
  entire derived arrows; no detection of morphism equality by evaluation is used.
- The counit e is `(system E X).adjunction.counit`. Its evaluation is the derived
  scalar adjunct of the total-limit projection by the existing `counit_projection`
  field. `integralComparisonReductionCounit_formula` identifies the *whole* counit
  with coefficient extension of `integralComparisonTowerCounit` and the ordinary
  extension/restriction counit. `integralComparisonTowerCounit_computes` computes
  the latter on every K-injective tower as the ordinary limit cone. Naturality
  transports this through any q: Res C→I, giving exactly `[q]⁻¹ ∘ (Δ lim I→I)`.
  This normalization is already true of these exact dependency declarations,
  so no additional arbitrary counit data is introduced.
- K in C_E(Y): `(K : sfIntegralConstructibleCategory l E Y)`, whose property is
  derived completeness, every positive constructible reduction, and one uniform
  finite cohomological interval. No finite-field datum or residue-characteristic
  parameter is introduced.
- `pullback_effective` asserts the three requested clauses for U_f R K in order:
  `IsNormalizedCoefficientSequence`, `sfIntegralConstructible` of its realization,
  and `IsIso` of its actual whole-system counit. `scalar_effective` asserts the
  same three clauses for S R K over L. Normalization is the canonical transition
  adjoint condition via the existing Hom-bijection definition; it is not a
  new copied notion of normalized DVR systems.
- `complete` is precisely `IsIso` of the actual completion unit at every allowed K.
- Natural descent through all representatives and common refinements is expressed
  by the natural realization isomorphisms and their normalization on *every*
  simultaneous presentation, and by the natural whole-system adjunction counit.
  The Roos comparison is likewise natural on the whole tower category and
  computed on every K-injective tower, so changing a tower resolution cannot
  change the comparison. In particular no family of unrelated evaluated maps
  is used to assert descent. All defining diagrams include the actual transitions.
- There is no finite Tor-amplitude, quotient flatness, or unramifiedness binder.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its imported coefficient constructions.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and completed quotient sheaves.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `CoefficientReductionPresentation`,
  `coefficientDerivedSystemEvaluationCalculus`, and the finite adjunctions.
- `Sheaf.Paper.NormalizedDVRTower`: `normalizedDVRRes`, `NormalizedDVRTower`;
  the existing `IsNormalizedCoefficientSequence` applies the same universal
  derived tensor/restriction criterion to a strict quotient diagram.
- `Sheaf.Paper.IntegralComparisonSequenceSystems`: the actual sequence derived
  pullback and scalar functors and their tensor-generator comparisons.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: `IntegralOnSlice.completedTensor`;
  its imported `integralDerivedPullback` is the operation in the primitive model.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`:
  `integralScalarExtensionOfUniverses`, inside the scalar model.
- `Sheaf.Paper.IntegralComparisonRealizationModels`:
  `IntegralComparisonRoosModel`, `IntegralComparisonPullbackModel`,
  `IntegralComparisonScalarModel`, `integralComparisonRoosBridge`, the normalized
  section transports, and the tower/reduction counit formulas named above.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients` (proof import).
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, inside the existing Roos normalization.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`, used by the primitive
  scalar model's actual universal counit.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its category.
  The convention node `def-weil-scheme-morphism-properties` fixes no declaration;
  scheme morphisms and invertibility are expressed directly as above.

Proof imports retain every currently stated proof dependency. The one unstated
proof prerequisite, `lem-trf-completion-unit-strict-quotient-model`, has no module
in the read repository; the theorem docstring retains that step. It is not a
statement prerequisite: the needed strict normalization is stated explicitly in
this theorem's own predicate. No downstream realization theorem is imported.

Universes and edge cases:

The assertion uses an arbitrary common ambient universe u for scheme and small
finite coefficient field models, as does the recorded intrinsic constructible
predicate. Its small pro-etale site still has objects in u+1 and morphisms in u;
module/quotient/derived universes are those of the dependencies, and are not
collapsed to the site's morphism universe. The normalization helper independently
supports a scheme universe t and coefficient universe u. Positive level n=0 means
A_(F,1). Identity scheme maps and E=L=M with identity embeddings are included;
no strict inclusion occurs. Composites E→M are included in the same family as
both successive inclusions. The zero complex and empty scheme satisfy all
hypotheses (invertibility is vacuous on the latter). Unbounded ambient K and
arbitrary representatives are permitted in the primitive and unit normalizations;
only effectivity uses the stated constructible-complete domain. Ramified finite
extensions are included without demanding flatness of A_(E,n)→A_(L,n).

Searches (2026-10-21):

- `msearch.py ... leanfinder` with query `Effective normalized Roos realization
  models for integral pullback and ramified scalar extension on proetale quotient
  systems`: eight ordinary etale-algebra hits, none matching this assertion.
- `msearch.py ... leansearch` with query `There exist simultaneous normalized Roos
  realization models for derived pullback and scalar extension`: eight ordinary
  ModuleCat scalar adjunction hits; none gives quotient-system realization models.
- `msearch.py ... loogle` with query `"IsKInjective", "lim"`: zero hits.
- `msearch.py ... grep` with pattern
  `IntegralComparison.*Model|effectiveComparisonRealization`: zero Mathlib hits.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for
  `effectiveComparisonRealization|EffectiveComparison|IntegralComparisonRoosModel`:
  the primitive interfaces and downstream consumers exist, but not this effective
  simultaneous existence assertion. The downstream `IntegralComparisonSystem`
  contains additional comparison data and does not state the explicit normalization
  and constructibility clauses here; it is not imported to avoid a dependency cycle.
- The prescribed node-id grep over `lean/WeilConjectures` found no match.

Validation: the first `scompile.py` pass elaborated both the sandbox and library
module without errors; it found one line-width warning, which was repaired.
The final `scompile.py` pass was clean in both sandbox (19.4 s) and library
(14.8 s) modes. `deliver2.py --no-push` returned `OK (dry run)` at
70c19a489de: preflight and per-file compilation passed; nothing was pushed.

## Second reading by Q25

I reopened the node and module for a separate clause-by-clause pass (no second
agent was started, following the dispatcher's explicit instruction). I checked
that the three effectivity conjuncts concern U_f R K and S R K themselves, not
merely isomorphic finite fibers, and that their IsIso is for the actual whole
counit. I checked the orientation of the initial unit formula: unit followed by
realization-to-Roos equals [v], equivalent to the node's formula with rho in the
opposite direction. The shifted coordinate is explicitly zero, including every
degree, rather than inferred from finite projections. The primitive model types
retain their universal representative and transition quantifiers. I checked
identity coefficient inclusions and ramified quotients, and found no extra Tor
or flatness hypothesis. No mathematical statement change was made. The only
compiler warning was a 102-character line; it was wrapped. The independent
maintainer review remains the independent reading of this delivery.
