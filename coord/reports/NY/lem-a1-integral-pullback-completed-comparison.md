## Worker report

The module `Sheaf.Paper.IntegralPullbackCompletedComparison` states
`WeilConjectures.IntegralCompletedComparison.integralPullback_completedComparison`.
Its proof is the sole `sorry` in the module. It asserts existence of the clause
package `IntegralCompletedComparison.Comparison`, rather than choosing an arbitrary
isomorphism and treating it as the canonical construction.

The source was read in `literature/stacks-project/proetale.tex`,
`lemma-pushforward-Noetherian-case` (Tag 099N), especially (2) and (5), including its
proof. The node's eleven-step proof, including the signed Roos normalization and
its canonical-map completeness argument, is reproduced in the theorem docstring.

Hypotheses and clauses:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite extension: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. Integers, uniformizer and positive quotient rings
  are the already defined Padic coefficient objects, not new coefficient choices.
- The schemes and morphism are `{X Y : Scheme.{u}} (g : X ⟶ Y)`. The theorem retains
  both invertibility hypotheses `_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x)` and
  `_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)`. There is no Noetherian,
  dimension, constructibility, boundedness, nonempty-scheme or immersion hypothesis.
- Completed coefficients and the ambient derived categories use the published
  `pbcIntegralDatum l E`, `PbcCompletedDerived` and the recorded integral module
  category. `modules`, `complexes` and `derived` are only aliases for restriction
  through the existing `ImmersionCompletedPullback.completedRingIso` and its exact
  derived functor. That ring isomorphism is fixed by every finite projection.
  The two presentations of K are therefore related by a specified coefficient
  equivalence. Restriction along the inverse ring isomorphism has restriction
  along its forward map as inverse, so this presentation includes every integral
  object and every morphism. It is not an extra hypothesis or a category of
  modules over the discrete constant integer ring.
- Derived completeness is precisely `IntegralOnSlice.IsComplete l E Y none` after
  that transport (`Complete` is an abbreviation). Its global branch is the
  recorded `IsDerivedCompleteUnrestricted` Roos-triangle condition; it has not
  been replaced by an assumed invertible completion unit.
- The conclusion `Comparison.intrinsic` proves
  `PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E) K` from that hypothesis.
  This predicate uses the recorded explicit Koszul completion and its unit.
  Thus the completed pullback's specified domain is justified in the conclusion.
- `integral` is exactly coefficient transport followed by `integralDerivedPullback`.
  `completed` is exactly `pbcActualCompletedPull` followed by the same output
  transport. The existing `pbcActualCompletedPullback_tower` comparison identifies
  the latter with `completedReductionTower ⋙ completedTowerPullback ⋙
  completedTowerRlim` on the intrinsic domain and preserves its unit. `towerIso`
  uses that already published unique normalized isomorphism.
- `Comparison.gamma` gives the requested isomorphism at every derived-complete K.
  `Comparison.naturality` is its naturality equation for every ambient derived
  arrow between any two such objects. These are isomorphisms and morphisms in
  the derived category of modules over the actual completed coefficient sheaf.
  In particular they retain the specified integral scalar action.
- Each `n : ℕ` means exponent `n + 1`, so all and only positive exponents occur.
  `finiteIntegral` and `finiteCompleted` are the two recorded exact finite
  pullback constructions after scalar restriction. `Comparison.finite` identifies
  them by a module natural isomorphism, and `finite_normalization` fixes that
  identification on each pulled-back tensor-unit generator. The two sides of
  `FiniteNormalization` use, respectively,
  `integralOperationsPullbackGenerator` on `1 tensor x` and the existing
  `completedReductionFiniteGenerator` on `1 tensor (1 tensor x)`. This excludes
  arbitrary automorphisms of a finite derived evaluation.
- `integralProjection` is the defining integral computation isomorphism on a good
  representative followed by `Q.map(mappingCocone.fst ≫ Pi.π ... n)`.
  `completedProjection` is the inverse strict-tower/reflector comparison,
  followed by the actual derived limit projection and the existing normalized
  `completedReductionFiniteEvaluation`, all transported through the same ring
  isomorphism. `finiteComputation` uses the existing universal reduction counit
  and exact restriction localization comparisons; it is not a chosen evaluation
  map. `Comparison.projections` says gamma inverse followed by the integral
  projection equals the completed projection, after the specified finite
  identification and computation maps. It quantifies over every good
  representative, not just a selected complex. Their computation maps are
  invertible there; essential surjectivity of the good resolving class and
  naturality give exactly the same equation at every K and every realization.
- `Comparison.chainShift_coordinates` fixes the integral shift by its two actual
  mapping-cocone coordinates. `levelShift` is the ordinary termwise additive
  shift comparison and `productShift` its canonical product comparison. The
  coordinates are `(x,y) ↦ (x,(-1)^r y)`, or `((−1)^r y,x)` in the node's cone
  order. `derivedShift_descent` fixes the derived shift using
  `integralDerivedPullbackComparison` on every shifted good representative.
  Finally `Comparison.shifts` states existence of completeness for K[r] and the
  required square between gamma at K[r], gamma at K shifted by r, and the
  completed-pullback shift. The completed side uses the existing normalized
  `pbcActualCompletedPullShift` of the cited triangle interface, combined with
  the exact coefficient restriction shift. Integer r is unrestricted.

Dependency declarations read and reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the imported integer, uniformizer
  and quotient definitions.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and its public coefficient
  imports: actual completed coefficient sheaves and their finite projections.
- `Sheaf.Paper.AdicCoefficientDatum`: completed reduction tower, reduction change
  functors and universal comparisons.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: its public original
  `WeilConjectures.integralDerivedPullback` and
  `WeilConjectures.integralDerivedPullbackComparison`.
- `Sheaf.Paper.PbcQbarCompletedPullback`: its public strict completed-pullback
  interface; no Qbar-stage or constructibility restriction is used.
- `Sheaf.Paper.DerivedCompleteOnSlices`:
  `WeilConjectures.IntegralOnSlice.IsComplete`, global branch.
- `Sheaf.Paper.IntrinsicCompletionCompleted`:
  `IsCompletedIntrinsicallyDerivedComplete` and its explicit unit, through the
  already published `PbcIsIntrinsicallyComplete` presentation wrapper.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`:
  `finiteCoefficientModulePullback_exact` and its coefficient-linear finite
  inverse-image interface.
- `Sheaf.Paper.CompletedPullbackTriangles`:
  `completedPullback_preserves_shifts_distinguished`, with the canonical
  unit-normalized shift supplied by its actual completed-pullback imports.
- The scheme-property node is a collector without a notion of its own. Schemes,
  morphisms and invertibility in stalks use the existing scheme/ring structures.
- Added recorded dependency `lem-sf-immersion-completed-pullback-comparison` only
  for `ImmersionCompletedPullback.completedRingIso` and `transport` in
  `Sheaf.Paper.SfImmersionCompletedPullbackComparison`. These helpers are defined
  for arbitrary morphisms/schemes; no immersion assertion is invoked. Both
  finite and completed coefficient identifications and their normalization were
  read. No dependency cycle is introduced.
- Added recorded dependency `lemma-weil-pbc-completed-pullback-reduction` for
  `completedReductionFiniteGenerator`, `completedReductionFiniteModelMap`,
  `completedReductionLimitProjection` and
  `completedReductionFiniteEvaluation`, in
  `Sheaf.Paper.CompletedPullbackReduction`. Their full normalization predicates
  and universal counit definitions were read. No dependency cycle is introduced.
- All already stated proof-dependency modules are imported for the eleven-step
  proof plan. Imports needed only by that plan are non-public. Mathlib supplies
  K-injectivity, quotient operations, exact sheafification and finite DVR quotient
  results. No missing dependency is replaced by a private copy.

Edge cases checked: zero K, empty source or target, identity g, n = 0 (exponent
one), unbounded complete complexes, r = 0, negative r and mixed-sign shifts.
No nonempty index or geometric point was required. Module maps on the empty site
are uniquely zero. The finite generator formula reduces to the tensor-unit
formula for the identity, and the zero-shift coordinate multiplier is one.
The category sizes follow the recorded common ambient universe convention:
site objects have universe u+1 and morphisms universe u; completed coefficients
and module values have universe u+1. No small-category instance identifying
site object and morphism universes is imposed.

Searches for an existing exact statement:

- `msearch.py ... leanfinder`, query “Integral derived pullback agrees naturally
  with strict tower completed pullback compatible with finite projections and
  shifts”: eight hits on integral scheme morphisms and ordinary presheaf/module
  pullback composition; none states this completed comparison.
- `msearch.py ... loogle`, query `SheafOfModules.pullback, Functor.CommShift`:
  service returned unknown identifier `Functor.CommShift`, no hits.
- `msearch.py ... grep`, query `integralDerivedPullback|completedPullback`: no
  Mathlib hits.
- `rg` for `integralDerivedPullback`, the item id and related completed comparison
  names in the upstream WeilConjectures tree: no exact statement. The separately
  prescribed `grep -rn` for the item id also returned no hits.
- `rg` in the side `lean/Sheaf` found the existing ordinary-versus-completed
  constructible theorem, immersion theorem and tensor comparison. None states
  this unrestricted complete-object comparison with the specified projection
  and shift equations. Their existing coefficient transport and finite
  evaluation constructions are reused instead of redefined.

A new definition node `def-a1-integral-completed-pullback-interfaces` is added. It records the existing declarations `AlgebraicGeometry.Scheme.ImmersionCompletedPullback.quotientEquiv`, `finiteRingIso`, `completedRingIso`, `transport`, and `AlgebraicGeometry.Scheme.completedReductionFiniteGenerator`, `completedReductionFiniteModelMap`, `completedReductionLimitProjection`, and `completedReductionFiniteEvaluation`. The node uses the exact published declarations and does not redefine them. The item now cites this definition node in `stmt_deps` in place of the two theorem nodes whose modules contain these helper definitions. There is no statement correction, dependency module, or STATEMENT-DISPUTED finding.

The required single-file scompile and deliver2 dry-run results are recorded by
the delivery tooling. All writes of this worker are confined to its sandbox.


## New nodes

`def-a1-integral-completed-pullback-interfaces` owns the canonical helper interface used by
the item. Its statement introduces the projection-normalized coefficient transport and the
normalized finite reduction generator, model map, limit projection, and evaluation isomorphism.
The node records existing declarations from `Sheaf.Paper.SfImmersionCompletedPullbackComparison`
and `Sheaf.Paper.CompletedPullbackReduction` through the primary declaration
`AlgebraicGeometry.Scheme.ImmersionCompletedPullback.completedRingIso`; no duplicate Lean
declarations are added.

## Second reading by NY

I reread the item statement and its updated dependency list after the repair. Every item clause
continues to use the same coefficient transport, finite generator, finite model map, limit
projection, and finite evaluation declarations. The two prior theorem dependencies are removed
from the item and are retained only as the definition node's source dependencies. The primary
existing declaration resolves in the published module, and all recorded helper names were read
in their defining modules. The new node has the item's chapter and unit, a self-contained
statement, three required search records, and no proof or hollow definition.
