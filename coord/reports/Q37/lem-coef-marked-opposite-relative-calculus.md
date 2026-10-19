## Worker report

The module `Sheaf.AlgebraicTopology.MarkedOppositeRelativeCalculus` states the node as
`SSet.Marked.Over.marked_opposite_relative_calculus : Nonempty OppositeRelativeCalculus`.
The structure bundles comparisons with their required naturality, coordinate normalizations,
and adjunction compatibility; its fields are the clauses of the node, not extra hypotheses.
The only postponed proof is this theorem. Its docstring contains all nine DAG proof steps.
`distinguishedFunctorInclusion` is the actual existing full-subcomplex inclusion, with real data.
`naturallyMarkedFibration` constructs the canonical naturally marked object over S,
with underlying E, projection p and exactly the distinguished-edge subset as its marking.
The theorem's `natural_marking` supplies only its proof-valued degeneracy field;
no data are selected from an unproved existence theorem. No new independent notion
or dependency replacement is introduced.

Hypothesis and clause correspondence:

- Small simplicial sets in the fixed universe are `SSet.{u}`. `u` is explicit and arbitrary.
  The theorem assumes no model structure, no quasicategory instances and no fibrancy hypothesis
  on arbitrary objects or bases. All marked-object and slice categories use this same universe.
- The horn and edge definitions are `Enhanced.IsCartesianEdge` and
  `Enhanced.IsCocartesianEdge` (final/initial horns for every n at least two, with the last/first
  ordered edge). `Over.IsDistinguishedEdge dual` selects these predicates. The already published
  `Over.relativeFibration dual` is exactly innerness plus prescribed-target/source base-edge
  lifts, with no quasicategory binders. `edge_reversal` and `fibration_reversal` give both duals.
- `Over.IsNaturallyFibrant dual X` means the given projection is such a fibration and that the
  marking is exactly its distinguished edges. `natural_marking` supplies the degenerate-edge
  condition for an exact natural marking; `natural_reversal` identifies these markings under
  reversal. `naturallyMarkedFibration dual p hp` then gives the actual object with this exact
  marking. Its only use of the theorem package is to fill a proof field, never to
  choose a simplicial set, subset or projection.
- `distinguished_maps` is preservation of every distinguished edge by a map commuting with
  the common projection; both its source and target are fibrations of the chosen kind.
- `Over.funOver` is the relative unmarked functor simplicial set, using minimally marked
  objects and flat parameter simplices. It has maps X times Delta[n] to Y over S in degree n
  for arbitrary total spaces. `Over.mapSharp` is Hom in the slice out of X times Delta[n] sharp.
  Both have the already defined restriction operators, not independently postulated operators.
- `Over.opposite` retains the degree-one marking through `opObjEquiv`, reverses the simplicial
  operators by `SSet.opFunctor` and reverses the projection. `equivalence`, `functor_eq`,
  `inverse_eq` specify the equivalence and its inverse. The latter uses the canonical double
  reversal identification S.op.op to S, required because Mathlib does not make this strict.
- `preserves_limits`, `preserves_colimits` assert preservation of all small universal cones
  and cocones, including empty ones. These are the degreewise limits/colimits of marked objects;
  their marking tests are described in the theorem's Step 2. `monomorphisms` preserves and
  reflects categorical monomorphisms, which are exactly degreewise injections here.
- `sharp_iso` is precisely MapSharp over S.op of reversed inputs to MapSharp over S opposite.
  `sharp_formula` identifies its component at every pair of degrees using the ordinal reversal
  `SimplexCategory.rev.map a`, so the isomorphism is the specified parameter-simplex reversal.
  `sharp_pre` and `sharp_post` express naturality in both inputs. `sharp_identity` and
  `composition_reversal` express preservation of identities and composition. `composition`
  has its full formula `g(f(x,t),t)` in `composition_formula`, so it is not arbitrary data.
- `tensor_iso` is the natural comparison O(X times K sharp) to O(X) times K.op sharp.
  `tensor_formula` is the identical pair of degreewise coordinates. `tensor_parameter`
  also identifies the parameter maps. These normalizations force unit-parameter and
  associativity coherence: both paths are the same coordinate maps.
- `cotensor` and `tensor_cotensor` state existence of the right adjoints to those actual
  tensor functors. Right adjoints determine their objects up to adjunction-compatible iso.
  `cotensor_iso` reverses cotensors, with both evaluation and coevaluation equations in
  `evaluation_reversal` and `coevaluation_reversal`. `mapping_adjunction`, `mapping_formula`,
  and `mapping_reversal` express the parameterized sharp-map adjunction and its reversal.
  These are the transposition identities for the relative exponential formula in Step 6.
- `functor_iso` and its `functor_formula` are the same opposite comparison on unmarked relative
  functors. `distinguished_iso` applies to naturally marked fibrations of either kind, so the
  existing `cartesianFunctors` is exactly the full subset on distinguished-edge-preserving
  maps. `distinguished_restriction` says this is a restriction of `functor_iso`, not a separate
  isomorphism. `core_iso` and `core_restriction` restrict it further to the actual enhanced core.
  No Kan claim is made about functor objects over arbitrary bases.
- `pushout_product` identifies the actual `Over.IsPushoutProduct` universal square and its
  outgoing arrow, after the tensor comparison at the codomain. Thus it asserts the canonical
  arrow identification rather than just an isomorphism of unspecified pushout objects.
- `push_iso` and `pull_iso` are natural isomorphisms with precisely the two composites in the
  node. `push_formula` is the identity on underlying coordinates; `pull_formula` identifies
  the projection to X and, since this is a morphism in the slice, also the projection to T.
  `base_adjunction` uses the actual `push` and `pull`; `base_unit_formula` and
  `base_counit_formula` give x to (p(x),x) and (t,y) to y. `base_unit_reversal` and
  `base_counit_reversal` explicitly intertwine both adjunction maps.
- `fiber_iso` reverses the degreewise vertex fiber, and `fiber_formula` identifies its total
  space projection. Its point coordinate is unique, so this specifies the canonical comparison.

Dependencies read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.fullSubcomplex`,
  `core`, `IsEquivalenceEdge`; Mathlib `SSet`, standard simplices, horns, internal hom.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`: `SSet.Marked`, `Hom`,
  `markedCategory`, `flat`, `sharp`, `product`, `productMap`, `sharpMap`, `sharpSimplex`.
- `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`, publicly reexporting
  `InfinityFibrations`: `Enhanced.IsCartesianEdge`, `IsCocartesianEdge`, `fiber`,
  `preservesCartesianEdges`, `preservesCocartesianEdges`, `cocartesianFibrationOver`.
  Its recorded declaration and full docstring were read; the imported relative primitives
  already extend both kinds, so no duplicate cartesian-fibration predicate was needed.
- `Sheaf.AlgebraicTopology.SimplicialOppositeHomotopyCalculus`:
  `SSet.simplicial_opposite_homotopy_calculus` (the full statement/docstring was read);
  Mathlib `SSet.opFunctor`, `opObjEquiv`, `opFunctorCompOpFunctorIso`, `opEquivalence`.
- Additional reused primitives from the published
  `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`:
  `SSet.Marked.Over`, `productLeft`, `mapSharp`, `mapFlat`, `mapVertex`,
  `productMapLeft`, `IsDistinguishedEdge`, `relativeFibration`, `IsNaturallyFibrant`,
  `unmark`, `funOver`, `PreservesMarkings`, `cartesianFunctors`, `push`, `pullObject`,
  `pull`, `oppositeObject`, `opposite`, `tensor`, `IsPushoutProduct`.
  Read the local complete module and confirmed its current source with `scompile.py --source`.
  The parent already defines all of these notions, so one-definition-per-notion requires reuse.
  No use of `marked_relative_cartesian_model` or its model package is made. The node's existing
  dependencies and statement remain unchanged. This is a definitional source import, not a new
  proof dependency on the downstream model theorem. The maintainer must omit the reverse
  proof-only import into that parent module when it would close the module import cycle,
  as permitted by stages/2-statements.md section 3 rule 7.

Edge cases checked before and after writing:

- Empty base and empty total space: everything remains a valid slice object; the fibration
  conditions quantify over actual base edges/vertices and impose no nonemptiness.
- Empty limit/colimit diagrams: the sharp base and the empty marked simplicial set are included.
- Dimensions zero and one occur in mapping objects and parameter formulas without bounds;
  only the existing outer-horn predicates impose n at least two. Reversal in dimension one
  exchanges the two endpoints and in dimension zero fixes the vertex.
- Degenerate edges are retained by `oppositeObject`, and exact natural markings contain them
  by `natural_marking`. Both cartesian and cocartesian choices are present.
- Bases and total spaces which are not quasicategories: no instance can accidentally exclude
  them. Full relative functor objects and cores are merely simplicial subsets in that case.
- Tensor parameters include the empty simplicial set, the point and arbitrary K; pushout
  products and base change use arbitrary maps, including identities. The coordinate formulas
  specialize to the identity comparisons in the identity and double-reversal cases.
- No independent smaller universe restricts a quantifier. The inverse explicitly handles
  the non-definitional double reversal of the base rather than imposing equality on it.

Searches (all fresh calls used Q37 and this item, so the launcher logs retain exact results):

1. `msearch.py ... leanfinder "Opposite equivalence of marked simplicial sets over a base,
   sharp mapping spaces, cartesian cocartesian horn reversal"`: eight hits on unmarked
   `SSet.opEquivalence`, `opFunctor`, `opObjEquiv`, `op_map` and related projections; no match.
2. `msearch.py ... loogle "SSet.opFunctor, SSet.Marked"`: zero hits; Mathlib does not contain
   `SSet.Marked` (the latter is project-owned).
3. `msearch.py ... grep "Marked|mapSharp|opFunctor" AlgebraicTopology/SimplicialSet`:
   eight hits on unmarked reversal and its monoidal instance; no marked relative theorem.
4. `msearch.py ... leansearch "marked simplicial sets opposite equivalence relative mapping
   object tensor cotensor"`: eight unmarked simplicial/opposite-equivalence hits, no match.
5. `rg` over `WeilConjectures`, `lean/Sheaf` and Mathlib for marked opposite, relative sharp
   maps, arbitrary-base fibration and the prospective new names: found the reusable parent
   primitives and the specialized relative nerve/cone comparison, but no full statement.
   `grep -rn` for the node id in upstream `WeilConjectures` returned none; the declaration
   names are absent from `dag/lean_names_upstream.json` and all three source trees.
   Mathlib `SimplicialSet/Op.lean`, `SimplicialObject/Op.lean`, `SimplexCategory/Rev.lean`,
   and the monoidal instance were opened to verify their definitions and conventions.

Source check: opened the official HTT PDF at
https://www.math.ias.edu/~lurie/papers/HTT.pdf, especially Definition the project server (arbitrary
simplicial bases), the relative mapping definitions preceding Remark the project server, and
Remark the project server (opposite convention). No source-based statement correction is needed.
No STATEMENT-DISPUTED issue was found.

Validation: `scompile.py` checked the file under its sandbox and library module names.
The first pass had only an unused binder warning in the cotensor family; renamed that
binder `_K`, retaining its explicit type. The final pass and delivery dry-run are recorded
by the prescribed wrappers. No direct local compiler or global build was run.

## Second reading by Q37

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
