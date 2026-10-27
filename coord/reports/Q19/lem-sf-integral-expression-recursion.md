## Worker report

The delivery states `integralExpressionRecursion` in
`Sheaf.SixFunctors.IntegralExpressionRecursion`, namespace
`WeilConjectures.IntegralSystemRealization.ExpressionRecursion`. Its only postponed
theorem is this item, with `by sorry`. Its docstring expands the DAG proof into the
finite-tree induction, unary and binary counit substitutions, simultaneous
coefficient identity, and comparison with the prescribed compactification map.
All helper data are actual definitions, recursive functions, or structures of
the given hypotheses. No dependency record or informal statement is changed.

The source is the coefficient-comparison sentence of blueprint main-20261015,
`sec-six-functors/sk-thm-sf-package/fix-prop-coherence.proof.md`, together with the
reviewed agent-formulated refinement in this node. This is the extracted recursion
obligation, not the structural-generator coherence theorem.

Hypothesis and clause correspondence:

1. The fixed algebraic closure of the finite field, its characteristic and the
   finite-field parameters are `D : FiniteFieldDatum.{u}`. The coefficient prime
   is `(l : ℕ) [Fact l.Prime]` with `_hl : l ≠ D.p`. The coefficient extension is
   `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
   The imported coefficient package fixes the integer ring, uniformizer, quotient
   rings and quotient maps. Level `n : ℕ` denotes the positive exponent `n + 1`.
2. Schemes and arrows over k are `Over (Spec (.of D.k))` and its morphisms. Every
   intermediate finite-type condition is retained in the existing
   `Expression.geometric`, as `LocallyOfFiniteType W.hom ∧ QuasiCompact W.hom`.
   Separated finite-type inverse images have exactly the three arrow properties
   in `Unary.pull`; `Unary.push` requires properness; `Unary.shriek` requires an
   open immersion and quasi-compactness. These mirror the existing expression
   constructors and do not require separated structure morphisms.
3. The categories are the recorded `System l E W` and `Integral l E W`, not
   levelwise systems of derived objects. `calculus` supplies the actual reduction
   functor, `coefficientSequenceLimit`, and their adjunction. Unit and counit
   components throughout are `.adjunction.unit.app` and `.counit.app` of that
   same calculus. The small pro-etale site is inherited through these packages.
4. The operations are `Unary.system` (the published `pull`, `Operations.push`,
   `Operations.shriek`) and `Unary.integral` (the published completed pullback,
   `ringedPush`, and `ringedOpen`). Tensor is respectively
   `.systemClosed.tensor` and `integralCompletedTensor`. Expression interpretation
   reuses `systemInterpretation`, `integralInterpretation`, and `Expression.evaluate`.
5. All inputs and intermediate conditions are exactly `e.domain l E o` and
   `e.geometric`. The former retains `sfIntegralConstructible`, `Good`, compatible
   etale origins, common finite cohomological and Tor bounds, and the hidden open
   intermediate of a compact-support constructor. No separate domain is invented.
6. The given natural primitive comparisons are `Primitives.unary` and `.tensor`.
   They are isomorphisms of the full-domain functors from basic realization.
   `.unary_spec` fixes the primitive map to `Unary.primitiveHom`: the recorded
   pullback/Roos model, actual right-adjoint-conjugate proper comparison followed
   by the inverse reconstruction unit, or actual open reduction followed by the
   inverse reconstruction unit. `.tensor_spec` fixes the canonical tensor model.
   The `RealizationModel` includes its published K-flat/ordinary normalization.
7. The given whole-system coefficient transformations are
   `Primitives.unaryReduction` and `.tensorReduction`. Their fields
   `.unaryTranspose` and `.tensorTranspose` state precisely
   `R.map d.inv ≫ e = r` on the primitive domains. Thus their restrictions are
   fixed by the prescribed comparisons and the actual counit; they are not
   arbitrary arrows substituted for those comparisons. The transformations retain
   naturality in their integral input or pair of inputs.
8. The four reconstruction assumptions are `Reconstruction.reduction`, `.limit`,
   `.unit` and `.counit`. They say R takes complete constructible inputs to Good
   systems, L takes Good systems to complete constructible inputs, and the actual
   unit and counit are invertible on exactly these respective domains. They are
   hypotheses of the node, not ambient reconstruction assertions.
9. The specified a-maps are actual definitions `unaryA` and `tensorA`:
   the inverse of L applied to the unary functor's counit image, or the tensor
   of the two counits, followed by the given d at L of the input(s). The shared
   published `GeneratorReduction.inverseOrZero` is the actual categorical inverse
   whenever its argument is invertible. Its zero branch makes the helper total
   outside its licensed domain; no theorem is asserted there. Invertibility on
   each required recursive domain is part of `Equations`.
10. `Comparisons` quantifies over every finite input type `I`, typed scheme family
    `X`, root scheme `W`, and finite expression `e`, and returns
    `e.realizationSource l E o ≅ e.realizationTarget l E o`. This is natural in the
    entire input family on the recorded full subcategory, rather than a family
    of unrelated objectwise isomorphisms.
11. `Equations` states the leaf equation using the inverse actual unit. Its pull,
    push and open cases state `a_A(M_V) ≫ A_int.map c_V`; its tensor case states
    `a_tensor(M_V,M_T) ≫ tensor.map (c_V,c_T)`. It recursively includes each child
    equation and licenses the applications at the reconstructed inputs with
    existential proofs of `basicUnaryDomain` or `basicTensorDomain`. Those proofs
    carry no extra mathematical hypothesis. The compact-support constructor
    expands into the same open then proper equations and keeps its hidden scheme.
12. `coefficientMap` is a genuine recursive definition of a morphism in `System`:
    identity at a variable; the primitive r followed by the operation applied
    to the child's r at a unary vertex; primitive tensor r followed by tensor of
    the two child maps at a binary vertex. The compact-support abbreviation uses
    that same open/proper composite. It does not construct a map by separately
    choosing maps at coefficient levels.
13. The main theorem concludes existence of the natural family `c`, its recursive
    `Equations` at every input, and the equality
    `coefficientMap ... = R.map ((c e g).inv.app K) ≫ e_(M_V)`. This is precisely
    the displayed `r_V = e_(M_V) R(c_V inverse)` with Lean's left-to-right
    composition. Because both sides are morphisms in the strict-system derived
    category, every quotient transition is retained before evaluation. At a leaf
    its identity is the adjunction triangle; no extra triangle axiom is assumed.
14. The prescribed direct d_c is `DirectComparisons.comparison`.
    `DirectNormalization` and `DirectProjection` reproduce the given normalization
    and finite scalar-adjunction-mate equations in `HasBasicRealizations`, with
    the actual open reduction map, proper-image comparison, evaluations and tower
    projections. They characterize the given primitive compactification comparison,
    not an independent freely chosen compact-support isomorphism.
    `SupportAgreement` identifies it with c at `supportExpression f cf`, followed
    by the already recorded `sfQcqsCompactSupportRealization`. `supportInput` is
    the actual inclusion of its primitive domain into the one-variable expression
    domain. Agreement is equality of the prescribed comparison components before
    finite evaluation, hence includes their morphisms and all transitions.
15. There is no hypothesis or conclusion about a structural generator, exchange,
    associator, projection diamond or their coherence. No such compatibility is
    needed to type the finite-tree recursion.

Dependency declarations read and used:

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`,
  `WeilConjectures.FiniteFieldDatum` and its existing field instances.
- `def-weil-l-adic-coefficient-extension`:
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing`, reexporting
  `Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionRing` and their transitions from `CoefficientExtension`.
  Only the coefficient constructions, not a fresh finiteness hypothesis, are used.
- `def-weil-scheme-morphism-properties` is explicitly a convention record; its
  named Mathlib classes are `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`,
  `IsProper`, and `IsOpenImmersion`. No missing declaration is replaced privately.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt` and `ProEt.topology` through the operation package.
- `lem-coef-derived-system-evaluation-calculus`:
  `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`,
  `CoefficientDerivedSystemCalculus`, `coefficientSequenceLimit`,
  `coefficientSequenceProjection`, finite derived evaluations, and the actual
  reduction/limit adjunction, used through the fixed `calculus`.
- `def-sf-integral-system-operations`:
  `Sheaf.SixFunctors.IntegralSystemOperations`, `System`, `Integral`, `Operations`,
  `pull`, `calculus`, `Operations.push`, `Operations.shriek`, `supportEvaluation`,
  and `compactOpenQuasiCompact`, all in `WeilConjectures.IntegralSystemRealization`.
- `def-sf-integral-system-expression-domain`:
  `Sheaf.SixFunctors.IntegralSystemExpressionDomain`, `Good`, `Expression`,
  `Expression.evaluate`, `Expression.geometric`, `inputReduction`,
  `Expression.domain`, `Expression.realizationSource`, `Expression.realizationTarget`.
- `lem-sf-integral-basic-realization`:
  `Sheaf.SixFunctors.IntegralBasicRealization`, `basicUnaryDomain`,
  `basicTensorDomain`, `basicSupportDomain`, `basicSupportInput`, `basicUnarySource`,
  `basicUnaryTarget`, and the prescribed comparisons in `HasBasicRealizations`.
  Its public imports expose the canonical bridge's `RealizationModel`,
  `RealizationModel.push`, `RealizationModel.openReduction`, `ringedPush`,
  `ringedOpen`, and the published pullback/tensor models.
- `def-weil-integral-rational-qbar-compact-support`:
  `Sheaf.Paper.QcqsCompactSupportRealization`, `sfQcqsCompactSupportRealization`,
  with the existing `sfCompactSupportFiniteIntegralFunctor`,
  `sfCompactSupportFiniteReductionIso` and `sfIntegralConstructible`.

Statement dependencies are publicly reexported by `IntegralBasicRealization`.
`GeneratorReductionStatement` is public because its existing `inverseOrZero`
occurs in the defining signatures. The three additional plain proof imports
are `RingedTowerPushforwardLimitComparison`,
`CompletedCoefficientPushforwardComparison`, and `IntrinsicCompactSupportRestriction`:
they supply the DAG proof tools for the strict proper-image/limit identification
and the finite scalar-restriction transitions. No cyclic proof import was added.

Edge cases checked before finalization:

- A leaf has exactly the actual inverse unit comparison and coefficient identity.
- An empty variable type admits no expression: there is no nullary constructor,
  so no zero-ary comparison is silently manufactured or excluded.
- Both children of a tensor may be the same expression or variable. No distinctness
  hypothesis is present, and the recursive function traverses both occurrences.
- Zero inputs, empty schemes and the identity or empty open immersion use the same
  constructors and full domains. There are no nonemptiness hypotheses on schemes.
- Single pull, proper image or open extension has the exact corresponding arrow
  hypotheses. In particular finite type is not confused with separated structure maps.
- The compactification constructor retains both its hidden open-extension object
  and its proper-image output. The geometricRoot helper reads existing conjunctions;
  it asserts no additional geometric theorem.
- The first finite level is n = 0 in Lean, meaning exponent 1. Equality in the
  actual system category also covers identity transitions m = n.
- No site/coefficient universe equality was introduced. The module uses the same
  universe convention as the recorded expression and operation packages.

Searches for an existing declaration (including the inherited search log):

- `msearch.py ... leanfinder "Recursive realization natural isomorphisms for typed
  expression trees under reduction limit adjunction counit"`: eight hits about
  adjunctions, equivalences and polynomial functors; none states this recursion.
- `msearch.py ... loogle "CategoryTheory.Adjunction.counit_naturality"`: generic
  counit naturality and two coequalizer hits; useful proof ingredients, not this
  statement or its strict-system compactification normalization.
- `msearch.py ... grep "expressionRealization|integralExpressionRecursion|RealizationModel"
  CategoryTheory`: no Mathlib hit.
- `rg` with `expressionRealization|integralExpressionRecursion|ExpressionRecursion`
  in `lean/WeilConjectures` and `lean/Sheaf`: no existing declaration of this item.
  Searching its DAG id in `lean/WeilConjectures` likewise found none.
- Direct source reading found and reuses the existing inverse helper,
  `GeneratorReduction.inverseOrZero`, and the expression/domain/primitive packages
  above. No missing independent notion or new definition node is needed.

No statement correction and no STATEMENT-DISPUTED finding.

Validation: the initial restored draft compiled successfully against the current
server sources in 45.4 seconds; the wrapper's older local snapshot timed out, and
its prescribed server confirmation passed. The final file is rechecked through
`scompile.py` and the required delivery dry run. Only the expected sorry warning
is permitted. Every universe and variable is bound with `autoImplicit false`.

## Second reading by Q19

I reopened the DAG statement, all helper definitions and the final theorem for a
separate semantic rereading. This is the dispatcher's single-worker rereading;
no independent worker is claimed, and the maintainer performs the independent
delivery review specified in the brief.

I checked the direction of every composition: a_A starts at L A M and ends at
A_int L M; the unary c starts there and ends at A_int V_int; r starts at
R V_int and ends at M_V. The open primitive uses the published open mate from
J R to R j_! followed by the inverse actual unit. The tensor uses the pair of
actual counits and preserves repeated variables. Direct support equality ends
at the recorded integral functor, with the canonical recorded realization as
its final factor. Its projection predicate is the equation from basic realization,
not a substitute family of arbitrary finite isomorphisms.

I compared all hypotheses and clauses against the numbered correspondence above.
I removed three unused domain wrappers (including an alias for integral
constructibility), so the final file uses the recorded predicates directly.
I checked that all recursive branches use the existing domain projections, and
that the compact-support branch keeps its hidden intermediate. No remaining
statement mismatch was found; the informal node is unchanged. The sole sorry
belongs to the matching DAG theorem, and all helpers have source/blueprint docstrings.
