## Worker report

This repairs the returned immutable head a3006148d637 (H3/H5). The saved
packet was inspected first and its prescribed dry run passed mechanically as
5b9775dd7d. The subsequent semantic self-check found that the report and
structure still had the defects described in the return. The accepted
universal quantification over the supplied calculus is retained; the free
normalizations and existential tautologies are replaced in the same module.

The module is `Sheaf.Paper.PurReductionLimitShiftAdjunction`. Its only
postponed theorem is `WeilConjectures.purReductionLimitShiftAdjunction`.
Its four supporting constructions have real data:
`purCoefficientLimitModel`, `purCoefficientShiftedResolution`,
`purCoefficientRoosProductShift`, and `PurCoefficientRoosTriangle`.
They are helpers for this node's specific normalization and triangle, recorded
in `lean.declarations`; they introduce no independent coefficient category,
reduction functor, derived limit, or derived-limit predicate.

The hypotheses and clauses are rendered as follows.

- The coefficient prime and finite extension are `l : ℕ`, `[Fact l.Prime]`,
  `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]` and
  `[FiniteDimensional ℚ_[l] E]`. The scheme is `W : Scheme.{t}`. As in the
  retained packet, the coefficient-calculus interface works on every scheme;
  the geometric specializations in the node require no extra construction.
  The theorem binds the already supplied
  `S : CoefficientDerivedSystemCalculus l E W` and its
  `hS : CoefficientDerivedSystemCoherence l E W S`.
- The actual completed ring, positive-index quotient rings, small pro-etale
  site, simultaneous ringed sequence site, strict module systems and ordinary
  derived categories are those of the imported coefficient-calculus and
  sequence-site declarations. In the source convention, Lean index `n`
  denotes quotient exponent `n+1`. The source's simultaneous ringed-site
  realization is the existing `coefficientSequenceModules`, used directly.
- `reduction_shift` is the structure on `S.reduction`.
  `finite_reduction_shift` supplies its finite comparisons, and now
  **`finite_shift_model` fixes each one against the pre-existing
  `coefficientFiniteReductionModel`**, on `Q` and `Q[r]`. Its equality starts
  at finite reduction of `Q(Q[r])`. One path uses localization's shift,
  the chosen finite comparison and the shifted K-flat model; the other uses
  the K-flat model of the shifted complex, the canonical termwise
  `mapHomologicalComplex` comparison and localization's shift. Thus there
  is an equality of actual morphisms involving the chosen finite comparison,
  not merely an assertion that a K-flat model exists.
  `reduction_shift_evaluation` then requires the recorded
  `S.reductionEvaluation n` to commute with the reduction shift and these
  fixed finite comparisons. The old `reduction_shift_model` field, which
  merely repeated `S.reductionModel`, is removed. The latter remains
  available from the supplied calculus for the proof.
- `limit_shift` is the structure on the actual `coefficientSequenceLimit`.
  **`limit_shift_resolution` fixes its morphisms using both `j` and exactly
  `j[r]`**, for every complex `N` and simultaneous K-injective replacement
  `j : U(N) → I`. The helper `purCoefficientLimitModel N I j` is explicitly
  `Rlim` applied to the exact restriction/localization comparison and `Q(j)`,
  followed by the existing `Functor.rightDerivedFunctorObjQIso lim I`.
  `purCoefficientShiftedResolution` is the canonical termwise identification
  `U(N[r]) → U(N)[r]` followed by `j[r]`. The field equates the path using
  the chosen `limit_shift.commShiftIso` and the shifted unshifted model with
  the model for this shifted replacement, followed by `lim`'s termwise
  shift comparison and `Q`'s shift comparison. This is precisely the
  `lim j[r]` normalization. There is no free auxiliary tower shift and no
  unused `tower_limit_shift` field.
- The K-flat proofs for `Q` and `Q[r]`, K-injectivity of `I` and `I[r]`,
  and quasi-isomorphism proofs of `j` and its shifted replacement occur
  only as inputs of the universal representative characterizations.
  Shift stability supplies them; they are not extra hypotheses on `S`,
  `W`, the source object or the target object. All integer shifts occur.
- `products` supplies the countable products in the actual coefficient
  derived category. `roos N I j` supplies a `PurCoefficientRoosTriangle`:
  its first vertex is literally `coefficientSequenceLimit.obj (Q.obj N)`;
  its other two vertices are the derived product of the evaluated tower
  `I`, and its middle map uses the actual tower transitions through
  `IsDerivedLimitTriangle`. Its `projection` equations fix every component
  of `p` by `purCoefficientLimitModel` followed by the actual limit-cone
  projection. Thus the triangle is attached to this functor, rather than
  quantified over an unrelated category and unrelated triangle.
- **`roos_triangle_shift` relates those actual triangles for `N,I,j` and
  `N[r],I[r],j[r]` using the very same `limit_shift`**. The product comparison
  is the real construction `purCoefficientRoosProductShift`: `Pi.mapIso`
  of localization's shift followed by the inverse of the product-preserving
  shift comparison. Its first equation fixes the shifted first arrow.
  Its second equation is the connecting-map square, with multiplier
  `r.negOnePow`, and the explicit `shiftFunctorComm _ 1 r` converting
  `[1][r]` into `[r][1]`. These equations have two already determined sides;
  they are not `∃ x, x = ...` tautologies. This is the Roos sign for the
  actual limit functor.
- `unit_shift` and `counit_shift`, for every `r : ℤ`, are the exact
  `Adjunction.CommShift.CompatibilityUnit` and `CompatibilityCounit`
  equations for `S.adjunction`, with these same normalized reduction and
  limit comparisons. They are equations of natural system transformations,
  without a finite-evaluation faithfulness assumption.

The theorem's docstring carries the proof route: the ordinary sequence-site
adjunction; K-flat computation and its finite normalization; exact scalar
restriction followed by the `j[r]` computation; the actual Roos triangles and
signed cone comparison; the derived-adjunction shift theorem; and edge cases.
No helper is proved using `sorry`. The only `sorry` is the main theorem.

Dependency declarations read and used:

- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `CoefficientDerivedSystemCoherence`,
  `CoefficientReductionModels`, `coefficientFiniteReductionModel`,
  `coefficientFiniteExtensionAdditive`. The finite model is the actual
  counit-based comparison on K-flat representatives.
- `Sheaf.Paper.CoefficientRingedSequenceSite`:
  `coefficientSequenceModules`, `coefficientSequenceRestriction`,
  `coefficientSequenceDerivedRestriction`, `coefficientConstantTowerLimit`,
  `coefficientSequenceLimit`, `coefficientFiniteDerivedExtension` and the
  recorded ordinary/unbounded localization instances. The normalization of
  `coefficientConstantTowerProjection_exists` was read as a model for the
  actual limit projections; the repaired triangle uses its chain formula.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`:
  `Functor.rightDerivedFunctorObjQIso`, with its actual signature and
  definition. It is a factor of the helper's real composite.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `IsDerivedLimitTriangle`, including its distinguished-triangle definition.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `ringedStrictTowerHomotopyLimitIndependentCoefficients`, the recorded
  independent-universe total-limit, K-injective and natural Roos interface
  (proof import).
- `Sheaf.Paper.DerivedAdjunctionShift`:
  `CategoryTheory.derivedAdjunctionShiftCompatible`, with its normalized
  derived Hom bijection and resolution-shift assumptions (proof import).
- Mathlib's existing `DerivedCategory.Q`, `mapHomologicalComplex`,
  `Functor.mapDerivedCategoryFactors`, `Limits.Pi.mapIso`, and
  `Limits.PreservesProduct.iso` provide the remaining canonical maps.

Edge cases: `r=0` gives identity comparison and sign +1; `r=1` and `r=-1`
both give sign -1 on the connecting morphism, while leaving termwise tensor
shift without an extra scalar sign. `Int.negOnePow` satisfies the addition
rule for repeated and negative shifts. The commutation map between `[1][r]`
and `[r][1]` is retained even though these shifts agree up to their canonical
identification. For zero complexes and the empty scheme all displayed arrows
are unique. Degree-zero sheaves and their one-step shifts are covered by the
same K-flat replacement formula. There is no quotient with exponent zero.
The coefficient universe remains `max u (t+1)`, and the site retains object
universe `t+1` and morphism universe `t`. As in the coefficient-calculus source,
the generic successor-universe sheafification instance is disabled so that
elaboration uses the already supplied coefficient-universe instance.

Searches from the saved packet remain in `searches.jsonl` (LeanFinder,
Loogle, grep of Mathlib, the upstream project and shared `lean/Sheaf`). The
repair additionally used LeanFinder with query “canonical shift comparison
for derived inverse limit computed on K-injective tower resolution”; its
8 hits were generic localization/exact-functor shift structures and K-injective
shift stability. Loogle with
`CategoryTheory.Functor.rightDerivedFunctorObjQIso, CategoryTheory.Functor.CommShift`
reported an unknown project identifier and no hits. The Mathlib grep query
`rightDerivedFunctorObjQIso|piComparison|negOnePow` in `CategoryTheory` returned
25 generic product-preservation and signed-triangle hits, including
`Triangle.shiftFunctor` and `PreservesProduct.iso`; these were opened to check
the sign and comparison directions. Direct `rg` of both
project source trees for the item, theorem and helper names found no existing
coefficient-specific statement or helper. Direct source searches found and
reused `rightDerivedFunctorObjQIso`, `Pi.mapIso` and `PreservesProduct.iso`;
none states the normalized coefficient adjunction theorem.

## Statement corrected

The previously accepted correction is retained verbatim. The old existential
conclusion could select a coefficient calculus; the corrected node asserts
the comparisons and unit/counit equations for every supplied calculus and its
coherence witness. Its source is the coefficient-comparison sentence of
`fix-prop-coherence.proof.md`, and the detailed resolution and sign calculation
in this node's proof. The present repair changes the Lean normalization fields,
not this already accepted correction or its proof route.

The complete citer audit by `rg -rl` found only
`lem-pur-integral-realization-shift-coherence`: holds true, because its use is
the shift compatibility for the coefficient calculus it has already fixed.
That node is not edited.

## Second reading by Q18

I reopened the saved node, the current source declarations and the repaired
module, and traced each normalization as a diagram of morphisms. This is the
worker's self-check, not a claim of an independent review agent.

The old `finite_reduction_shift` was free: transporting `reduction_shift`
through `S.reductionEvaluation` could satisfy its only condition. That no
longer suffices: `finite_shift_model` includes the chosen shift on the left
and the fixed counit-based K-flat models and termwise shifts on the right.
Changing the finite shift also changes a constrained morphism in this square.
The old repeated `S.reductionModel` assertion is gone.

The old limit condition merely chose a named projection and then chose a
canonical chain shift. It never used `limit_shift`. The new equality does
use its component, with source and target checked against the explicitly
constructed resolution comparisons for `j` and `j[r]`. Choosing a right-adjoint
shift by the abstract adjunction does not discharge this fixed normalization.
The previously unused tower shift has been removed.

The old Roos clause held by choosing its two existential maps. It is replaced
by a triangle with actual sequence-limit first vertex, actual evaluated tower
transitions, and actual normalized limit projections. Its shift equations
use that triangle and the chosen `limit_shift`, with the signed connecting
map and the canonical shift commutation explicitly present. The arbitrary
ambient category and its unused universe variables have been removed.

The unit/counit fields still refer to the supplied `S.adjunction`; they now
constrain the same comparisons that occur in all three representative/triangle
squares. The helpers use canonical composites and product isomorphisms, with
no arbitrary-map or Nonempty choice. The declaration list and verbatim theorem
signature were updated. No new node, dependency replacement or additional
statement correction is required.

Validation: the repaired full module passed `scompile.py Q18
lem-pur-reduction-limit-shift-adjunction <module>` in both sandbox and library
confirmation, with no diagnostics (library confirmation 30.5 s). The packet
self-check verified the verbatim recorded signature, complete declaration
list, maximum 100-character lines, and exactly one postponed theorem proof.
