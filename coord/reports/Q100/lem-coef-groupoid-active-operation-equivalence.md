## Worker report

The module `lean/Sheaf/CategoryTheory/GroupoidActiveOperationEquivalence.lean` states
`CategoryTheory.OperadGroupoidActiveOperationEquivalence.groupoid_active_operation_equivalence`.
It uses the four recorded statement dependencies and the existing coherent operation
subcomplex.  The helper declarations in the same module are canonical constructions
belonging to this operation-space notion:

* `stringNerve`, `operatorNerve`, and `stringOperatorMap` are respectively
  `N_hc(D(G))`, `N_hc(O_G^\otimes)`, and `N_hc(\Phi_G)` from the operator-nerve and
  pair-operator models.  `operatorPairVertex` is defined as the image of the string
  pair vertex under this map; `FunctorModel.objects` identifies it with the explicit
  pair color `(P.color (x,y))`.
* `fixedArityOperations` is the full simplicial subcomplex of the recorded
  `operations q C` selected by `inputArity q C a = n` on every vertex.  Its inclusion
  is `fixedArityInclusion`.  Thus the definition retains all coherent triangles,
  source-change equivalences over identities, and all higher simplices.
* `IsFixedArityOperationMap` characterizes a comparison by the equation on
  `operationArrows`; this is the actual postcomposition map induced by `f`, rather
  than an arbitrary map between vertex sets.
* `sourceArrowSpace` and `targetArrowSpace` are the pullbacks of the two endpoint
  evaluations of `(ihom Δ[1]).obj X` along the specified constant vertices.  `constantPathMap`
  is the closed-category curry of projection `Δ[1] × X → X`, and
  `positiveProductMap` is identity on the two endpoint factors and this constant-path
  map on every internal factor.

The theorem's binders render the node as follows.  `N` is the coherent-nerve
comparison datum; `O` is its normalized operator/string statement; `G` is an arbitrary
small simplicial groupoid and `hG` is its fibrancy hypothesis; `P` and `F` are the
pair-color multicategory and the explicit enriched functor supplied by
`operad_groupoid_operator_map`.  For every `x y : G` and `n`, the positive-arity
hypothesis is `0 < n`.  The first existential map `e` has exactly the fixed-arity
operation spaces as source and target.  `IsFixedArityOperationMap` renders “induced by
`f`” and `IsFunctorEquivalence e` renders equivalence of the full coherent spaces.
The maps `a` and `b` identify the two spaces with
`A_x × X^(n-1) × B_y` and
`A_x × Fun(Δ¹,X)^(n-1) × B_y`; their three `IsFunctorEquivalence` clauses include
that the product comparison is an equivalence.  The equation
`e ≫ b = a ≫ positiveProductMap ...` renders identity on the endpoint factors and
constant paths on all internal factors.  `Fin (n - 1)` gives the empty product when
`n = 1`.

The final conjunction handles `n = 0` separately.  `e₀` is the induced nullary map
and is an equivalence.  Maps `a₀` and `b₀` identify both nullary operation spaces
with `arrowMappingSpace X (N.vertex G.carrier x) (N.vertex G.carrier y)`; the equation
`e₀ ≫ b₀ = a₀` states that the induced map is the normalized span-to-arrow map.  The
explicit `ba⁻¹` and `h ↦ (x,1_x,h)` formulas are the `nullary` and `FunctorModel`
formulas in the recorded `OperadGroupoidOperatorMap` dependency, and the
`IsFixedArityOperationMap` equation retains them on all coherent simplices.

Dependencies used directly are:

* `Sheaf.CategoryTheory.CompleteAlgebroid`:
  `CategoryTheory.CoherentNerveComparisonStatement`, `CoherentNerve.nerveFunctor`;
* `Sheaf.CategoryTheory.SimplicialOperatorNerve`:
  `CategoryTheory.SimplicialOperatorNerve.Statement` and its `string_model` and
  `operators` fields;
* `Sheaf.CategoryTheory.OperadGroupoidOperatorMap`:
  `PairModel`, `FunctorModel`, `nullary`, and
  `operad_groupoid_operator_map`'s explicit formulas;
* `Sheaf.CategoryTheory.OperadicLocalizationOperationCriterion` and its imported
  `OperadicOperationSegalProduct`: `operations`, `operationArrows`, `inputArity`,
  and `IsFunctorEquivalence`/`IsOperationMap` conventions;
* `SSet.Enhanced.arrowMappingSpace`, `evaluation`, `fullSubcomplex`, and the
  Cartesian closed structure are imported from the recorded dependency modules.

The proof dependencies are imported as plain imports as required by the stage plan:
`Sheaf.CategoryTheory.JoinSliceRightFibration`,
`Sheaf.CategoryTheory.SpaceTransportClassification`,
`Sheaf.AlgebraicTopology.PathFibrationReplacement`, and the modules already public
through the statement dependencies.  The only postponed proof is the theorem proof,
which is `by sorry`.

Edge cases checked before writing were: `n = 1` (the internal `Fin 0` product is
terminal and the product comparison is endpoint identity), `n = 0` (the separate
span normalization clause), repeated endpoints `x = y`, empty mapping spaces, and an
empty groupoid (the universal quantification over `x,y` is then vacuous).  No
nonemptiness, connectedness, or characteristic hypothesis was added.

Searches for an existing declaration were:

* `msearch.py ... leanfinder "fixed arity active operation spaces of a simplicial
  groupoid string operad and pair colored multicategory equivalence"`: eight generic
  nerve/groupoid hits, none matching this statement;
* `msearch.py ... loogle "operationSubcomplex, fixedArityOperations,
  IsFixedArityOperationMap"`: zero hits (the project notion is not in Mathlib);
* `msearch.py ... grep "fixedArityOperations|groupoid_active_operation_equivalence"
  CategoryTheory`: zero hits;
* `rg -n` over `WeilConjectures/` and `lean/Sheaf/` for the helper and theorem names:
  no existing declaration of this item; the only related matches are the canonical
  `operationSubcomplex` and the localization criterion;
* `grep -rn "lem-coef-groupoid-active-operation-equivalence"` over the source
  repository: no upstream declaration.

No new definition node or dependency repair is needed.  `STATEMENT-DISPUTED:` none.

## Second reading by Q100

I reread the node, all four statement-dependency records, and the complete module.
The small fibrant simplicial groupoid, coherent nerve/operator models, explicit
string-to-pair map, positive-arity condition, and separate nullary condition are all
present.  Fixed arity is imposed through the actual source ordinal of the existing
coherent operation subcomplex, so higher triangles and simplices remain.  The map
characterization is an equality on `operationArrows`; it does not permit an unrelated
map.  The positive comparison uses identity endpoint maps and `constantPathMap` on
exactly `Fin (n - 1)`, while the nullary comparison is separately normalized to the
arrow mapping space.  The module compiled cleanly with `scompile.py`; no mismatch or
statement correction was found.
