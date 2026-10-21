## Worker report

The module `Sheaf.Paper.FiniteExpressionReductionComparison` states
`WeilConjectures.FiniteExpressionReduction.finiteExpressionReductionComparison`.
It defines only the owning statement's system evaluation, completed evaluation,
recursive beta and coherent gamma. The single postponed proof is the named item
theorem, with the complete seven-step node proof in its docstring. All definitions
have actual data. No statement correction, dependency repair or new DAG node is needed.

The source is the current blueprint main-20261015, order 2232,
`sec-six-functors-basics/sk-def-purity-conv/def-weil-frobenius-coefficient-twists.md`,
read in full. Its last sentence concerns compatibility with finite reduction. As
its source record explicitly says, this item is an agent-extracted finite-expression
argument, not a quoted blueprint theorem. The module documents that distinction.

Hypothesis and clause correspondence:

- Prime and finite extension: `(l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`. The integer ring, uniformizer,
  positive finite coefficients and completed sheaf are the dependency's existing
  constructions. The natural-number level `n` throughout that API means exponent
  `n+1`; thus level zero represents the required first quotient, not exponent zero.
- Schemes and invertibility: `{S : Type s} (W : S → Scheme.{t})` and
  `_hInvertible : ∀ a x, IsUnit (l : (W a).presheaf.stalk x)`.
  Universes `s`, `i`, `t`, `u` are explicitly declared and independent. There is no
  nonempty, finiteness, finite-field, characteristic, boundedness or constructibility
  hypothesis added to the contexts or systems.
- Ordinary whole semilinear systems: `coefficientSequenceDerived l E (W a)`.
  This is the ordinary derived category of modules on the vertical ringed sequence
  site, not a category of towers of objects in an already-derived category.
  `IsNormalizedCoefficientSequence` is the existing Hom-bijection formulation of
  invertible actual quotient-transition adjoints, including all pairs and cocycles.
- Reduction and total limit: `D a : CoefficientDerivedSystemReduction l E (W a)`
  retains the canonical finite scalar-extension evaluations, K-flat reduction model,
  reduction functor and adjunction to `coefficientSequenceLimit`. The latter is the
  recorded total right-derived limit after exact whole-system scalar restriction.
- Specified primitive maps: `ρ a : PrimitiveCounit.RoosRealization ...` and
  `C f : PrimitiveCounit.Comparisons ...` use the recorded primitive theorem's exact
  interfaces. The fields `tensor_model` and `geometric_model` pin the realizations
  on the actual quotient complexes and Roos comparison; this is no arbitrary map
  or objectwise choice of an isomorphism. For tensor use `(C (𝟙 (W a))).tensor`;
  for geometric pullback use `(C f).geometric`. The tensor component of that record
  is independent of the geometric morphism. Its `tensor_iso`, `geometric_iso` and
  naturality fields package the node's assumption that these specific primitives
  are natural isomorphisms on normalized inputs. Its `counit_effective` packages
  the canonical normalized-system effectivity from the dependencies. Other fields
  of this supplied canonical presentation are already conclusions of the recorded
  primitive theorem; they impose no new geometric or normalization condition.
- The three normalization closure assumptions are precisely `hUnit`, `hTensor`
  and `hPull`. The unit uses the existing `ringedSiteDualityUnit` directly, so no
  second definition of the coefficient unit is introduced. Tensor is
  `(D a).systemClosed.tensor`, whose finite evaluations and K-flat model are in D;
  inverse image is the recorded `PrimitiveCounit.pull` on actual whole systems.
- Finite typed syntax is the dependency's `CompletedOperations.Expression W location a`.
  `systemValue` sends input k to `N k`, unit to the coefficient unit, tensor to
  the system tensor, and pullback to `PrimitiveCounit.pull`. `completedValue`
  sends input k to its total limit, unit to the total limit of that unit, tensor
  to `integralCompletedTensor` and pullback to `integralDerivedPullback`.
  These are the actual global quotient-complex/Roos operations publicly retained
  by the recorded `IntegralDerivedOperationsOnSlices` module; that module's slice
  completion form has a canonical comparison with these global operations.
- The prescribed beta is `beta`: identity at inputs and units; at a tensor the
  completed bifunctor image of both child beta maps followed by
  `PrimitiveCounit.tensorBeta`; at a pullback the completed inverse-image of the
  child beta followed by `PrimitiveCounit.pullBeta`. These dependency definitions
  are exactly realization followed by total limit of the operation on counits.
  There is no reassociation or replacement of the prescribed composites.
- The prescribed gamma is `gamma`: `(D a).reduction.map (beta ...) ≫`
  `(D a).adjunction.counit.app (systemValue ...)`. It is a morphism of whole
  ordinary derived systems before any evaluations are taken.
- Every normalized input is quantified by `N` and `hN`. The theorem's four
  conjuncts state normalization of the system value, `IsIso beta`, `IsIso gamma`,
  and the actual transition square for every `{m n : ℕ} (h : n ≤ m)`.
  The square is `eval_m.map gamma ≫ tau_target = tau_source ≫ Res.map (eval_n.map gamma)`,
  exactly the displayed equation in the node under Lean's left-to-right composition.
  Both source and target of tau are explicitly given, so equality is not obtained
  by assuming evaluations faithful or by reconstructing a map from its evaluations.
- The induction parameter is explained explicitly in proof step 1 of the docstring:
  inputs zero, units one, tensor one plus both child sizes, pullback one plus child
  size. Both children are smaller even if they coincide. The statement uses the
  inductive finite syntax and hence quantifies over all such expressions. Its
  actual recursive data retains the specified parentheses. No tensor/limit
  exchange or faithfulness assumption appears anywhere.

Dependency declarations read and used (including their complete signatures and
docstrings):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and the publicly retained coefficient
  integer, uniformizer and quotient constructions. The scheme-morphism-properties
  dependency is explicitly a collector with no notion or declaration of its own;
  `Scheme` and scheme morphisms use the existing AlgebraicGeometry API.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, with its completed-ring and finite
  constant-sheaf sources. The present statement uses these coefficients through D.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `SemilinearSections.semilinearDerivedSections`, the whole-system calculus;
  its concrete coefficient incarnation is `coefficientSequenceDerived`,
  `coefficientSequenceDerivedEvaluation` and `coefficientSequenceDerivedTransition`.
- `Sheaf.Paper.NormalizedDVRTower`: `NormalizedDVRTower`, `normalizedDVRRes` and
  the canonical quotient cocycle interfaces. For whole derived systems the existing
  `IsNormalizedCoefficientSequence` is the corresponding normalization predicate;
  it adds no irrelevant finite-field datum to this item's statement.
- `Sheaf.Paper.IntegralReductionTowerCanonical`: `canonicalIntegralReductionTower`,
  the actual strict quotient reduction tower, retained by the primitive comparison.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `ringedStrictTowerHomotopyLimitIndependentCoefficients`, the proof dependency
  supplying the total-limit/Roos background; imported without `public` here.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemReduction`, its `reduction`, `adjunction`,
  `reductionModel`, `reductionEvaluation`, `systemClosed`, and `evaluationTensor`;
  the complete recorded theorem is `coefficientDerivedSystemEvaluationCalculus`.
- `Sheaf.Paper.NormalizedDVREffectivity`: `normalizedDVRTower_effectivity`, whose
  coherent counit conclusion is retained in the primitive comparison record;
  imported as a proof dependency. No strengthened boundedness assumption is used.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: `IntegralOnSlice.completedTensor`
  and its global comparison; its public import retains `integralCompletedTensor`
  and `integralDerivedPullback`, which are the normalized quotient/Roos operations
  used by `PrimitiveCounit.tensorBeta` and `PrimitiveCounit.pullBeta`.
- `Sheaf.Paper.CompletedOperationExpressions`: `CompletedOperations.Expression`,
  read with all four constructors and its independent scheme/input index universes.
- `Sheaf.Paper.CompletedPrimitiveCounitComparison`:
  `PrimitiveCounit.Comparisons`, `RoosRealization`, `pull`, `tensorBeta`, `pullBeta`,
  and `completedPrimitiveCounitComparison`; read their full fields and docstrings.

Edge cases checked before writing: a single input and a single unit have identity
beta; gamma in those cases is the actual counit. With no input indices, unit,
tensor and pullback expressions remain valid and `hN` is vacuous. With no scheme
indices there is no output a, hence no typed expression. For `tensor (input k)
(input k)` the two occurrences independently use the same input, with no inequality
requirement. Nested pullbacks and tensors keep their parentheses by the actual
recursive definitions. At `m=n` the same natural transition is included, with the
canonical identity scalar restriction; no strict inequality was used. Empty schemes
are permitted. Levels start at quotient exponent one, and scheme, coefficient,
scheme-index and input-index universes remain independent.

Searches made through the required msearch.py wrapper for this item:

- LeanFinder, "Finite typed tensor pullback expressions have recursively invertible
  counit comparisons on normalized coefficient systems": eight hits, ordinary
  linear tensor splitting, polynomial tensor models and free monoidal normalization;
  none is the typed completed-operation theorem with its coherent system counit.
- Loogle, "CategoryTheory.Functor.map_isIso, CategoryTheory.Adjunction.counit":
  two generic adjunction inverse-counit/unit formulas, no matching expression theorem.
- Mathlib grep, "finiteExpression|reductionComparison|completedValue|systemValue"
  in CategoryTheory: zero hits.
- LeanSearch, "Finite typed tensor pullback expressions preserve normalized systems
  and recursively defined counit comparisons are isomorphisms": eight hits on
  categorical pullbacks, simplicial finite products and abelian tactic expression
  syntax; none is this theorem.
- Project rg on those names and this node id in both `lean/WeilConjectures` and
  `lean/Sheaf`: upstream has no matching theorem; the parent module
  `CompletedOperationTowerSubstitution` has expression evaluators with a different
  operation presentation (`CompletedOperations.Models`, slice completion tensor and
  `integralComparisonDerivedSequencePullback`). Its `ComparisonLaws` record includes
  normalization, invertibility and transition fields as part of the stronger parent
  conclusion, not a theorem under the present primitive and closure hypotheses.
  This item is its newly extracted proof dependency: importing the parent would
  reverse that intended dependency, and its stronger structural models are not the
  present hypotheses. The helpers here evaluate the recorded primitive presentation
  directly, using all existing tensor, pullback, unit, reduction and limit definitions.
  They do not introduce a second coefficient construction or a new notion of syntax.

There are no node faults or disputed statements. Initial server scompile completed
cleanly in both sandbox and library-module modes (4.2 and 4.3 seconds). After the
final direct dependency imports and removing a redundant coefficient-unit alias,
the final module is compiled again by scompile and the required delivery dry run.
The worker delivers directly; independent mathematical review is the maintainer's
review, as requested in the current brief.

## Second reading by Q02

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
