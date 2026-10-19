## Worker report

The module `Sheaf.CategoryTheory.PatternInducedFibrationTest` defines the
induced cone index `InducedConeIndex`, the inner-horn consequence
`quasicategory_of_fibered_object`, the induced fully scaled pattern
`inducedPattern`, and the transported object `inducedObject`.  Its main
statement is `fibration_iff_induced_fibered`.

The node's hypotheses and clauses are rendered as follows.  `P` is the
small categorical pattern `CategoricalPattern.{u}`.  `Y` is an object over
`P`, and `hY : IsCategoricalPatternFibered P Y` is the four-clause fibered
hypothesis.  `K` and `hK : ModelStatement P K` supply the model structure from
the model-calculus dependency.  `f : X ⟶ Y` is a marked map over `P`, with
`X` another `CategoricalPattern.Object P`.  The induced pattern has carrier
`Y.underlying.underlying`, marking `Y.underlying.marking`, scaled set
`Set.univ`, and cone index `InducedConeIndex P Y`.  An index consists of an
`alpha : P.index` and a map `q` whose composite with `Y.map` is
`P.left_cone alpha`, together with the clause
`∀ e, q.app _ e ∈ Y.underlying.marking`.  Its cone is `P.cone alpha` and its
left-cone map is `q`.  `inducedObject hY f` retains `X.underlying`, uses
`f.map` as its map to the induced carrier, and uses `f.preserves` for marking
preservation.  The first side of the equivalence is exactly
`hK.model.categoryWithFibrations.fibrations f`; the second is exactly
`IsCategoricalPatternFibered (inducedPattern P Y hY) (inducedObject hY f)`.
No condition on cocartesian lifts over edges outside `Y.underlying.marking`
appears in the statement.

The dependency declarations used are:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`,
  `SSet.Enhanced.coneCategory` and its recorded helper declarations.
* `Sheaf.CategoryTheory.CategoricalPatternFibrancy`,
  `SSet.Enhanced.CategoricalPattern`, `CategoricalPattern.Object`, and
  `IsCategoricalPatternFibered`.
* `Sheaf.CategoryTheory.CategoricalPatternModelCalculus`,
  `SSet.Enhanced.CategoricalPattern.categorical_pattern_model_calculus`,
  `ModelStatement`, and its recorded model/enrichment declarations.

Edge cases checked: `P.index` and each cone may be empty; the sigma/subtype
index then has no elements and remains a valid small type.  An empty cone is
retained as `P.cone alpha` and is not dropped.  `Set.univ` includes all
2-simplices, including degenerate ones.  The marking field already contains
degenerate edges by the dependency structure.  The construction does not
assume that any edge outside the marking has a cocartesian lift.  The
quasicategory helper uses the standard theorem that an inner fibration over a
quasicategory has a quasicategorical total space.

Searches for an existing declaration were made before writing the module:

* `msearch.py Q37 lem-coef-pattern-induced-fibration-test leanfinder "A map to a fibrant marked simplicial object over a categorical pattern is a fibration exactly when fibered for the induced pattern"`: returned only generic model-category and Kan-fibration declarations; no categorical-pattern result.
* `msearch.py ... loogle "HomotopicalAlgebra.Fibration"`: returned generic model-category fibration predicates, with no induced-pattern statement.
* `msearch.py ... grep "CategoricalPattern|pattern.fibered|induced.pattern"`: zero matching declarations in Mathlib.
* `rg -n "pattern.*induced|induced.*pattern|CategoricalPatternFibered|IsCategoricalPatternFibered" lean/Sheaf /home/ubuntu/weil-src-slopmaster2/WeilConjectures`: found only the recorded categorical-pattern definitions and consumers; no fibration-recognition theorem.

The module was compiled with `scompile.py`; it completed without errors or
warnings after the line-width and instance-linter fixes.

## Second reading by Q37

I reread the node statement, the induced-pattern definitions, and the final
Lean signature.  `P`, `Y`, and the fibered hypothesis are present; the
projection equality and the all-edges-marked clause are both present in
`InducedConeIndex`; all 2-simplices are scaled through `Set.univ`; and the
map `f` is transported without changing its marking.  The equivalence uses
exactly the supplied model fibration predicate and the four-clause induced
fibered predicate.  No cocartesian-lift requirement outside the marking was
added.  Empty index and cone cases remain represented by the unchanged sigma
and cone fields.  No mismatch was found.

## Maintainer review fix

The maintainer's second reader (cc review service, 2026-10-18) repaired the module in
place. The mathematics and the construction are unchanged.

* H3: the node assumes "S contains every equivalence edge of C". The delivered signature
  left this out, and `CategoricalPattern` does not contain it. The theorem now takes
  `hS : ∀ e : P.carrier _⦋1⦌, IsEquivalenceEdge P.carrier e → e ∈ P.marked`, written
  with the recorded `SSet.Enhanced.IsEquivalenceEdge` of def-cbc-enhanced-diagrams-cones.
  Step 5 of the node's proof uses this hypothesis to make `f` an isofibration. Without
  it the Lean claimed more than the node and its proof give, for every pattern.
* H8: the theorem's docstring now gives the node's nine proof steps. Each helper's
  docstring now names its source place (HA B.0.27 / B.2.7).
* `lean.statement` and `lean.note` are updated in the same way.
