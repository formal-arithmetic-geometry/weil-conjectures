## Worker report

The delivery states `WeilConjectures.completedPrimitiveCounitComparison` in
`Sheaf.Paper.CompletedPrimitiveCounitComparison`. Its proof, and the named structural
lemmas needed to construct the geometric system inverse image, are `sorry`. All
functors, maps, transports, and predicates have real definitions. Every declaration
is listed in the node's `lean.declarations` and has the item's blueprint annotation.
The node's mathematical statement, dependencies, and proof are unchanged.

Hypotheses and objects, in the order of the statement:

- The prime is `l : ℕ` with `[Fact l.Prime]`. The finite extension is `E : Type u`
  with `[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The existing
  `Padic.coefficientExtensionRing` supplies the valuation-ring quotients and their
  fixed uniformizer; `n : ℕ` denotes exponent `n+1`, including the first quotient.
- `X Y W : Scheme.{t}` and `f : X ⟶ Y` are arbitrary. `_hX`, `_hY`, and `_hW`
  say precisely that `l` is a unit in every stalk. There are no finiteness,
  separatedness, smoothness, or boundedness assumptions. The object and morphism
  universes of each small pro-etale site remain `t+1` and `t`; the coefficient
  universe `u` is independent.
- The completed coefficient ring is the existing unrestricted limit
  `unrestrictedIntegralCoefficientRing`; `scalarReductionSource l E W` is its
  module-sheaf category. The finite rings, scalar extensions and restrictions are
  those of `CoefDerivedSystemEvaluationCalculus` and `IntegralReductionTowerCanonical`.
- The ordinary unbounded whole-system category is `coefficientSequenceDerived`.
  Its underlying module sheaves on the vertical sequence site retain all quotient
  morphisms. `S.systemClosed.tensor` is its derived tensor, computed by the
  existing `systemTensorModel` on K-flat complexes. `S` and `V` are the existing
  `CoefficientDerivedSystemReduction` calculus records on W and Y: they provide
  the specified canonical reduction, adjunction and normalized representative
  models. These universally quantified records package constructions supplied by
  the dependency theorem; they are not new hypotheses on a complex, on a map,
  or on a coefficient ring.
- `IsNormalizedCoefficientSequence` is the already defined transition-adjoint
  criterion: for every n≤m, every test complex and every degree, precomposition
  with the transition gives the scalar-extension universal Hom bijection.
  Identity and cocycle equations are supplied by the whole-system object itself.
  Thus this predicate expresses the stated normalization without adding the
  obsolete finite-base-field parameter of `NormalizedDVRTower`.
- The system geometric inverse image is `PrimitiveCounit.pull`. Its ordinary
  precursor is the left adjoint of the explicitly constructed sectionwise
  `PrimitiveCounit.direct`. `base`, `ringComponent`, and `ringMap` use actual
  pro-etale base change and the canonical finite constant-section ring map.
  `section_eq` is the explicit section identity used for transports.
  `inverse_exact` allows the ordinary inverse image to induce the unbounded
  derived functor. `inverseEvaluation_existsUnique` fixes its finite evaluation
  comparison by the evaluated actual adjunction unit, not an arbitrary choice
  of isomorphism. `inverseEvaluation` chooses this uniquely characterized
  comparison. `inverseComplexEvaluation` is its ordinary chain-complex extension.
- Reduction R is `S.reduction` or `V.reduction`. Its actual quotient representatives
  and all quotient transitions are retained by `CoefficientReductionPresentation`.
  L is the existing `coefficientSequenceLimit`, namely derived restriction followed
  by `coefficientConstantTowerLimit`. The counits are the single whole-system
  natural transformations `S.adjunction.counit` and `V.adjunction.counit`.
  The calculus records' `counit_projection` equations already identify every
  evaluated counit as the scalar-extension adjunct of the actual total-limit
  projection. These equations are retained as data, not replaced by a new adjunct.
- The completed operations are `integralCompletedTensor` and
  `integralDerivedPullback`, the actual quotient-complex/Roos descended functors.
  They are publicly retained by the recorded dependency module
  `IntegralDerivedOperationsOnSlices`. This module's
  `IntegralOnSlice.completedTensor_global_comparison` identifies its global slice
  specialization with the same `integralOperationsTensorOnGood` representative
  model. We use the original global descent and its specified comparison, which
  exposes exactly the actual finite-tensor tower required by this node.

Conclusions and normalization clauses:

- `PrimitiveCounit.Comparisons.tensor` is the natural functor isomorphism r_T from
  the actual completed tensor to
  `S.reduction.prod S.reduction ⋙ S.systemClosed.tensor ⋙ coefficientSequenceLimit`.
  `.geometric` is r_F to `V.reduction ⋙ pull ⋙ coefficientSequenceLimit` on X.
  They are natural isomorphisms of entire functors, not per-object or per-level
  existence statements. `.geometric_evaluation` records the stated finite
  derived inverse-image description of this actual system pullback.
- The theorem produces `RoosRealization` on W and X. Its `.comparison` is natural
  on complexes of strict restricted towers. `roosF` is the existing shifted cone
  of 1-s on the actual countable product. `roosBridge` is the definitional identity
  with `integralOperationsRoosFunctor`. `.projection` requires preservation of
  the existing total-limit projections and `roosEval` maps.
- `RoosRealization.resolution` quantifies every quasi-isomorphism q into every
  K-injective tower I. It requires the comparison after q to equal C(q), followed
  by the inverse of Q(`roosι I`), the actual termwise-limit identification, and
  the canonical derived-functor comparison. `roosι` is the pre-existing inclusion
  with zero shifted coordinate. No termwise-injectivity or boundedness condition
  is imposed on I. The extra generality over the displayed injective-resolution
  form of `strictRoosComparison` follows by homotopy equivalence to a termwise
  injective K-injective resolution; both lim and Roos preserve that equivalence.
- `TensorModel` quantifies every good pair P,Q, where good means flat-term K-flat.
  It gives simultaneous whole-system complexes C,D, their K-flatness, their
  identifications with reductions, finite quotient presentations, and an actual
  strict restricted-tower isomorphism z to `integralOperationsTensorTowerFunctor`.
  `CoefficientReductionPresentation` pins the presentations at all quotient
  transitions. The component equation for z is `restrictEvaluation`, followed
  by the canonical ordinary `coefficientEvaluationTensorIso`, the tensor of the
  quotient presentation maps, and `finiteTensorBridge`. The latter is literally
  `Iso.refl` between the two existing finite scalar-restricted tensor definitions.
  Consequently z cannot absorb arbitrary levelwise or sign automorphisms.
- `PullModel` makes the analogous assertion for every good P, using the actual
  `integralOperationsPullbackTowerFunctor`. Its component equation uses the
  unit-normalized `inverseComplexEvaluation` and the quotient presentation.
  In both models the final equation is the representative comparison of
  `IntegralOperationsWellDefined`, followed by the real Roos map of z inverse,
  equal to r followed by the derived restricted representative identification
  and rho inverse. This pins the realizations on every representative and gives
  resolution independence through the dependency's unique-compatible descent.
- `tensorBeta` is exactly r_T at `(L A,L N)` followed by
  `L.map (T.map (e_A,e_N))`. `pullBeta` is exactly r_F at L C followed by
  `L.map (pull.map e_C)`. There are no arbitrary comparison arrows in these defs.
- `Comparisons.counit_effective` and `.geometric_counit_effective` assert that
  the actual counits are invertible for normalized systems.
  `.tensor_iso` and `.geometric_iso` assert invertibility of these exact beta maps
  under exactly the displayed normalization hypotheses.
- `.tensor_inverse` and `.geometric_inverse` quantify isomorphisms whose forward
  maps equal the actual counits and specify the beta inverse as the image of
  their inverse maps followed by r inverse. The direction and order agree with
  the displayed formulas in the node. Existence of those counit isomorphisms
  follows from the preceding effectivity fields.
- `.tensor_naturality` and `.geometric_naturality` are the beta naturality squares
  for all whole-system maps. `.counit_naturality` and
  `.geometric_counit_naturality` explicitly give the counit equation in the
  whole derived system category before evaluation, with no normalization
  assumption on either endpoint.
- `.projections` and `.geometric_projections` give the naturality equation for
  `coefficientSequenceProjection` at every n, with the necessary finite scalar
  restriction visible on the right. Together with the existing calculus
  `.counit_projection`, these retain the exact coefficient-extension adjunctions.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; the public coefficient construction
  uses `Padic.coefficientExtensionRing` and its quotient homomorphisms.
- `def-weil-scheme-morphism-properties` has a convention record, not a Lean
  declaration; schemes and morphisms here use Mathlib `Scheme` and `X ⟶ Y`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`; its public completed coefficient
  modules supply `unrestrictedIntegralCoefficientRing` without a finite-base-field
  parameter or an equality of the site and coefficient universes.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `SemilinearSections.semilinearDerivedSections`, the general whole-system theorem.
  The concrete sequence category and tensor models are the existing specialization
  in `CoefDerivedSystemEvaluationCalculus`, not private duplicate definitions.
- `Sheaf.Paper.NormalizedDVRTower`: `NormalizedDVRTower`, read alongside the
  equivalent unrestricted `IsNormalizedCoefficientSequence` from
  `Sheaf.Paper.CoefficientRingedSequenceSite` publicly used by the calculus.
- `Sheaf.Paper.IntegralReductionTowerCanonical`:
  `canonicalIntegralReductionTower`, its maps and canonical quotient transitions.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `coefficientDerivedSystemEvaluationCalculus`,
  `CoefficientDerivedSystemReduction`, `CoefficientReductionPresentation`,
  `coefficientSequenceLimit`, `coefficientSequenceProjection`,
  `coefficientConstantTowerLimit`, `coefficientConstantTowerProjection`,
  `coefficientConstantTowerEvaluationFactors`, `coefficientSequenceRestriction_evaluation`,
  and `coefficientEvaluationTensorIso`.
- `Sheaf.Paper.NormalizedDVREffectivity`: `normalizedDVRTower_effectivity`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`:
  `IntegralOnSlice.completedTensor`, `completedTensor_global_comparison`, and
  the publicly retained `integralCompletedTensor`, `integralDerivedPullback`,
  `integralCompletedTensorComparison`, `integralDerivedPullbackComparison`.
- `Sheaf.Paper.IntegralOperationsWellDefined`: `integralOperationsWellDefined`,
  `integralOperationsGoodComplex`, `integralOperationsTensorTowerFunctor`,
  `integralOperationsPullbackTowerFunctor`, `integralOperationsRoosFunctor`,
  `integralOperationsLevelPullback`, and `integralOperationsLevelPullback_additive`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`:
  `Scheme.ProEt.countableProducts_exact`.
- `Sheaf.CategoryTheory.StrictRoosComparison`: `CategoryTheory.strictRoosComparison`;
  `Sheaf.CategoryTheory.StrictRoosModel`: `roosF`, `roosι`, `roosEval`.
- Proof imports also include `KFlatResolutionIndependentCoefficients` and
  `ChangeOfRingsKFlatIndependentCoefficients`. The geometric helper uses the
  existing independent-universe `Scheme.coefficientProEtaleModulePullback`,
  `coefficientProEtaleModuleDirectImage`, `coefficientProEtaleModuleAdjunction`,
  `coefficientProEtaleDirectRingMap`, and
  `coefficientProEtaleModulePullback_exact`.

Edge cases checked before and during writing: n=0 is exponent one, so no zero
quotient is accidentally inserted; m=n uses the identity transition. Zero complexes
and zero maps give zero beta and projection equations with isomorphisms between
zero objects. Empty schemes make the stalkwise invertibility assumption vacuous
and leave the same canonical sheaf constructions. Identity f gives the ordinary
identity inverse image up to its unit-normalized universal comparison. No assumption
on an input being bounded, normalized except where stated, constructible, or
perfect has entered. Distinct site and coefficient universes remain allowed.

Searches for an existing statement and constructions:

- `msearch.py NB ... leanfinder` on completed derived tensor/pullback as inverse
  limits of coherent systems with natural counit comparisons: eight ordinary
  adic-completion hits, including `AdicCompletion.ofTensorProduct`; no match.
- `msearch.py NB ... loogle` on
  `CategoryTheory.Adjunction.counit_naturality, CategoryTheory.Functor.map_isIso`:
  zero hits. General counit naturality is insufficient for the representative
  realization and the specified completed operations.
- `msearch.py NB ... grep` on
  `StrictRoos|completedTensor|totalLeftDerivedCounit`: three hits in Mathlib's
  `CategoryTheory/Functor/Derived/LeftDerived.lean`; no sheaf-system comparison.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for primitive/counit/completed
  comparison names and the item's id found no existing statement of this node.
  It found the actual Roos descents, strict Roos model and evaluation-calculus
  declarations reused here. The legacy geometric specialization fixed
  `E : Type (u+1)` and could not be used at independent site/coefficient sizes;
  the actual sectionwise geometric map supplied here keeps those sizes independent.
- Searches for sequence pullback/evaluation exposed no already defined canonical
  specialized independent-universe system geometric pullback. Its structural
  helpers therefore occur in this owning node's module with its blueprint id,
  as authorized by the brief, rather than introducing a second system category
  or replacing the canonical map by arbitrary existence data.

Validation: scompile.py compiled both sandbox and library module presentations
without errors or non-sorry warnings. Final dry-run and delivery results are
recorded by deliver2.py. No statement dispute or node correction is required;
no new node or dependency-record repair is included.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
