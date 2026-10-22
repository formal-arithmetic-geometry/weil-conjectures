## What changed

Replaced `tensor_comparison_localization_descent` by an assembly proof using the actual
constructed `rationalDatum`, its separately stated normalized validity, and common-stage
construction. The existing theorem signature and public imports are unchanged.

Constructed and proved the localized symmetric monoidal category and bilinearity;
the balanced rational functor, its laws, perfectness and finite-dimensional range;
the semilinear transitions, their additive Hom API, tower cocycle and identity;
the transition tensor cores; the perfect-subcategory scalar core and rational tensor
core; and the natural rational scalar-square comparison. The canonical exact-field
comparison is derived by the left-derived universal property and is normalized on
every complex. All object-valued definitions are actual constructions. The new composite scalar
core is named and irreducible. Mathlib's existing oplax composition and
CoreMonoidal.ofOplaxMonoidal construct it from the lifted integral comparison and
perfect scalar extension. Tensor induction extends its naturality to the actual
rational Hom modules.

The packet changes no existing definition, target statement, or source-library module.
The parent retains its original command header; its two added imports are private
proof imports. An exploratory global linter override was removed after preflight
identified it as an interface change, and the proof uses an ordinary local `let`.

## Proved and sorry left

Closed the sole body hole of
`WeilConjectures.TensorComparisonDescent.tensor_comparison_localization_descent`.
Its assembly proof is complete, but this is a decomposition: one upper hole is replaced
by two strictly smaller remaining results, so holes closed minus holes added is 1 - 2 = -1.

Two holes remain in the packet, each exactly a named public theorem with `by sorry`:

- `WeilConjectures.TensorComparisonDescent.rationalDatum_normalization`, node
  `lem-sf-rational-comparison-normalization`: eight scalar normalization equations for
  the already explicitly constructed datum. The other 24 validity clauses are proved
  in `rationalDatum_valid_of_equations`, and `rationalDatum_valid` combines them. No
  data is chosen from the normalization theorem.
- `WeilConjectures.TensorComparisonDescent.common_tensor_comparison_construction`, node
  `lem-sf-common-tensor-comparison-construction`: common-stage source and target monoidal
  construction and its 21 formulas, assuming an already valid rational datum.

All other declarations added in this packet have complete proofs. The validity
assembly proves bilinearity, conditions 1--9, 13--22 and 26--29 directly; the remaining
eight conditions are the scalar normalization obligation. The pre-existing
perfect scalar coherence theorem remains an imported proof dependency.

Every retained Lean module is checked with lcompile.py in import order.
The independent server delivery checks are run by deliver3.py.

## No longer needed

No existing module or node is withdrawn. The original six proof dependencies remain
needed transitively through the new nodes; the parent now depends directly on the
concrete rational construction, its validity and common-stage construction.

Exploratory identity/tower normalization and validity-clause proof files were not
retained as additional obligations. The unused integralPerfectFunctor and
integralPerfectCore wrapper definitions were replaced by the generic composite
constructor. The unused experimental projection APIs and generic explicit
composition helper are also omitted. No unused exploratory module is imported.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies mostly provide definitions and interfaces. They do
not contain a theorem constructing the common-stage monoidal structure or packaging
the rational normalization clauses. Those are the two genuine remaining statements.
The eleven-step route is preserved, organized as rational construction and common-stage
descent. No mathematical statement is disputed and no unit route is bypassed.

The attempted additional normalization proofs exposed expensive kernel conversion
when specializing the monoidal dictionaries (33.6 seconds for one inverse tensor
formula). Those proof experiments and their unused specialized APIs are not retained.
The retained core constructors and validity assembly avoid those specializations;
the file time limit and heartbeat limit are unchanged.

Edge cases reviewed: zero arrows and zero scalar coefficients are included in the
tensor-induction proofs; equal fields use the original identity components rather
than a strict identity transition; arbitrary derived arrows are covered by naturality
of the scalar comparisons. Common-stage independence must use a further compositum
for incomparable fields, as stated in the remaining common-stage proof.

## New nodes

`lem-sf-field-perfect-scalar-comparison` attaches `Sheaf.Paper.FieldPerfectScalarComparison`: For a homomorphism of fields, the actual fixed-second-factor derived scalar functor B is canonically isomorphic to exact termwise field scalar extension; on every representing complex its composite with mapDerivedCategoryFactors is the recorded modelMap.

`lem-sf-rational-comparison-transition-tensor` attaches `Sheaf.Paper.RationalComparisonTransitionTensor`: Each actual rational coefficient transition is strong monoidal with tensor and unit comparisons equal to the integral comparisons tensored with one.

`lem-sf-perfect-scalar-monoidal-functor` attaches `Sheaf.Paper.PerfectScalarMonoidalFunctor`: The fixed derived scalar functor restricted to perfect source objects is strong monoidal with the recorded balanced tensor and unit maps as inverse tensorators. A perfect-valued strong monoidal functor lifts to the full perfect subcategory.

`lem-sf-rational-comparison-datum` attaches `Sheaf.Paper.RationalComparisonDatum`: A valid integral comparison determines an explicit RationalData record: balanced functors, perfect and finite-dimensional range, tensor cores, localized stage system, transition cores, identities, exact-field comparison and rational phi.

`lem-sf-scalar-localization-monoidal` attaches `Sheaf.CategoryTheory.ScalarLocalizationMonoidal`: Extend a linear symmetric monoidal category along localization of its Hom modules. Objects, tensor objects and the unit stay fixed; tensor of pure arrows multiplies coefficients; constraints are tensored with one. The result is symmetric monoidal and bilinear.

`lem-sf-rational-comparison-structures` attaches `Sheaf.Paper.RationalComparisonStructures`: For the finite integral coefficient categories of IntegralData, the fixed raw rational categories carry the explicit symmetric monoidal localized structures, with all object, pure-arrow, associator, symmetry, unitor and bilinearity formulas.

`lem-sf-rational-comparison-stage-system` attaches `Sheaf.Paper.RationalComparisonStageSystem`: The actual rational transitions form a stage system with the integral tower components tensored with one and the integral equal-stage identity components tensored with one.

`lem-sf-rational-comparison-functor` attaches `Sheaf.Paper.RationalComparisonFunctor`: A valid integral comparison extends to the actual localized Hom modules by a tensor f mapped to coefficientEquiv(a) times the derived fraction-field extension of F(f). This is additive, perfect-valued and has bounded finite-dimensional cohomology.

`lem-sf-rational-comparison-transition` attaches `Sheaf.Paper.RationalComparisonTransition`: Each integral coefficient transition extends semilinearly to the actual rational categories. A pure arrow b tensor f maps to equiv_L inverse(fieldMap(equiv_E(b))) tensor T(f), and the transition is additive.

`lem-sf-rational-comparison-scalar-square` attaches `Sheaf.Paper.RationalComparisonScalarSquare`: The two integral-to-field extension paths give a natural comparison phi for the actual rational transition functors, with components obtained from the integral phi, the two normalized scalar tower maps and the exact field scalar comparison. Exact field extension preserves the perfect image.

`lem-sf-common-tensor-comparison-construction` attaches `Sheaf.Paper.CommonTensorComparisonConstruction`: For any valid rational comparison R, the actual source pair quotient and finite-stage target pairs carry CommonStructures and CommonData satisfying all 21 specified common-stage formulas.

`lem-sf-rational-comparison-valid` attaches `Sheaf.Paper.RationalComparisonValid`: For every valid integral comparison A, the explicit rationalDatum A hA satisfies every field of RationalData.Valid, namely all 31 prescribed object, morphism, tensor, symmetry, transition, identity, tower, scalar-square and model normalization equations.

`lem-sf-localization-left-derived-comparison` attaches `Sheaf.CategoryTheory.LocalizationLeftDerivedComparison`: For a localization L and a left-derived functor LF of F with counit alpha, an isomorphism beta from L followed by G to F determines LF isomorphic to G, with normalization L applied to the comparison followed by beta equal to alpha.

`lem-sf-rational-comparison-tensor` attaches `Sheaf.Paper.RationalComparisonTensor`: The explicitly balanced rational comparison is strong monoidal; its tensor and unit comparisons are obtained by composing the integral comparison with actual derived fraction-field scalar extension.

`lem-sf-rational-comparison-normalization` isolates the eight scalar equations left
after the 24 directly proved validity clauses. The validity theorem itself now has
a complete constructor proof.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
