## Worker report

The module is `lean/Sheaf/AlgebraicTopology/SegalHomotopyCategoryComponents.lean`.
It uses the already recorded Segal-space declarations from
`Sheaf.AlgebraicTopology.SegalCategoricalEquivalence`; it does not redefine a
simplicial space, a Reedy-fibrant predicate, a strict mapping fiber, a homotopy
category, an induced functor, or the equivalence-arrow subcomplex.

The module adds three postponed statements.

* `SSet.Segal.homotopyFunctor_map_fiberEdge` takes Segal spaces `U` and `V`,
  a simplicial-space map `f`, vertices `x,y` of `U_0`, and a point `a` of the
  strict mapping fiber.  Its equality says that the existing functor
  `homotopyFunctor f` sends the class `fiberEdge U x y a` to the class of the
  mapped point under `mappingFiberMap f`.  This renders the clause that every
  map of such spaces induces the functor determined by its maps on objects and
  mapping spaces.
* `SSet.Segal.equivalenceSubcomplex_mappingFiber` takes a Segal space, two
  vertices, an arbitrary inner degree `q`, and a simplex `a` of
  `mappingFiber W x y`. Its left side is membership of the underlying simplex
  in the existing `equivalenceSubcomplex W`; its right side says that every
  vertex of `a` has invertible `fiberEdge` class. This identifies the strict
  fiber of `W_eq` with the full subcomplex on isomorphism components in every
  degree, including degree zero. `homotopyCategory_homs` ensures that the
  invertibility predicate is constant on each mapping-fiber component.
* `SSet.Segal.homotopy_category_components` takes a Reedy-fibrant Segal space
  `W` and an equality of `SSet.π₀` classes for arrows `g,g'` in `W_1`.  It
  concludes `IsIso (edgeClass W g) ↔ IsIso (edgeClass W g')`, with no equality
  of source or target vertices.  This is the main conclusion of the node.

The node's setup clauses are rendered as follows.  `Space` is the functor
`SimplexCategoryᵒᵖ ⥤ SSet`; `IsSegal W` is the conjunction of the recorded Reedy
matching-map fibrancy and weak-equivalence consecutive-edge maps for every
`n ≥ 2`.  The vertices are `(W.obj (op ⦋0⦌)) _⦋0⦌`.  `mappingFiber W x y` is the
strict fiber of `(d₁,d₀)` and `fiberEdge` identifies its components with
homotopy-category morphisms.  The existing `homotopyCategory W` has these
objects and `homotopyCategory_homs` supplies the stated `π₀` morphism sets,
identities, and composition; the existing `homotopyFunctor` supplies
functoriality.  `equivalenceSubcomplex W` is the union of the components
containing an isomorphism.  The two added helper theorems make the functorial
and strict-fiber clauses explicit, while the main theorem states component
invariance.

The hypotheses and clauses are unchanged from the node: arbitrary small
simplicial sets and Kan complexes are inherited through the recorded
`Enhanced.IsWeakHomotopyEquivalence`; Reedy fibrancy and every consecutive-edge
weak equivalence are bundled in `IsSegal`; no completeness assumption is added.
The component condition is exactly `SSet.π₀.mk g = SSet.π₀.mk g'`, and the
conclusion is an iff of invertibility, so neither direction is weakened and
arrows with different endpoints remain allowed.

Dependencies used by declaration:

* `def-cbc-enhanced-diagrams-cones`: `SSet.Enhanced.IsWeakHomotopyEquivalence`
  and the subcomplex constructions used by the recorded Segal-space module.
* `lem-coef-kan-quillen-right-proper`: the recorded Kan--Quillen classes used
  in `SSet.Segal.IsReedyFibrant`.
* `lem-coef-reedy-model-structure`: `HomotopicalAlgebra.Reedy.matchingFrom`,
  used by the recorded Reedy-fibrancy predicate.
* The stated proof dependencies are imported without `public`:
  `Sheaf.AlgebraicTopology.SimplicialSpaceReedyCartesian`, declaration
  `SSet.SegalSpace.reedy_cartesian_simplicial`, and
  `Sheaf.AlgebraicTopology.KanRealizationSerre`, declaration
  `SSet.kan_realization_serre`.
* The previously landed module
  `Sheaf.AlgebraicTopology.SegalCategoricalEquivalence` supplies
  `SSet.Segal.Space`, `IsSegal`, `mappingFiber`, `mappingFiberMap`,
  `homotopyCategory`, `homotopyCategory_homs`, `fiberEdge`, `edgeClass`,
  `equivalenceSubcomplex`, and `homotopyFunctor`.  This is an existing
  project declaration, so no private copy or new dependency node was made.

Edge cases checked: the statement permits an empty simplicial space and empty
mapping fibers; it imposes no nonemptiness at degree zero; `n = 2` is included
by `2 ≤ n`; the equality of `π₀` classes allows paths changing both endpoints;
constant/identity arrows are included in `equivalenceSubcomplex`; and the
statement does not assume completeness.  The strict-fiber helper is quantified
for every pair `(x,y)`, including pairs with no arrows.

Searches made:

* `msearch.py ... leanfinder "Segal space homotopy category invertibility
  constant on path components of arrows"`: returned Mathlib strict-Segal and
  truncated-homotopy-category declarations, but no Segal-space component
  theorem.
* `msearch.py ... loogle "SSet.Segal homotopyCategory edgeClass IsIso"`: no
  result; Loogle reported the project namespace as unknown.
* `msearch.py ... grep "Segal.*homotopy.*category|IsIso.*component"
  AlgebraicTopology`: no Mathlib hits.
* `rg` over `WeilConjectures/` and project `lean/Sheaf/` found no declaration
  named `homotopy_category_components` or
  `equivalenceSubcomplex_mappingFiber`; the existing
  `SegalCategoricalEquivalence` module was read in full and reused.
* `grep -rl '"lem-coef-segal-homotopy-category-components"' dag/nodes`
  found the four known citers (outer-horn, complete-levelwise,
  composition-equivalences, and categorical-equivalence-dk); no statement was
  corrected and no new node was needed.

`scompile.py` compiled the module cleanly with the expected postponed proofs;
there were no errors, timeouts, or non-sorry warnings.

Continuation self-check (2026-10-17): retained the saved packet and first ran
the prescribed dry run. Read the current node and the existing Segal-space
module, along with the recorded statement-dependency interfaces; the saved
node differs from the current node only in `lean`. Checked Rezk Sections
5.1--5.8 and (6.3) at the node's source URL. The saved strict-fiber helper
only restated the definition of membership in `W_eq`. Replaced that helper
with the exact isomorphism criterion above, in every simplicial degree, and
expanded the proof docstrings to include the zigzag inverse criterion and
the moving-endpoint path lifting. Added the two already stated proof imports.
The main statement and all natural-language node fields remain unchanged.
There are no new definitions, dependency modules, or statement corrections.
All universes and variables are explicit, and all theorem proofs remain
`sorry`. Repeated `scompile.py` after these repairs: both the sandbox and
library-path checks passed, with no diagnostics. The previous reading below
is retained as part of the saved packet;
the separate second reader must check these continuation repairs before delivery.

## Earlier second reading (a previous round; superseded)

I reread the item statement and the complete recorded declarations.  The
`W : \\Delta^{\\mathrm{op}}\\to\\mathrm{sSet}` object is exactly `SSet.Segal.Space`;
`IsSegal` supplies Reedy fibrancy plus all degree-`n ≥ 2` spine maps.  The
objects, strict fibers, `π₀` morphisms, degeneracy identities, and degree-two
composition are those of `homotopyCategory`, `mappingFiber`, and
`homotopyCategory_homs`.  The induced functor is the recorded
`homotopyFunctor`, and the first helper checks its action on the exact fiber
representatives.  The hypotheses on `g,g'` use only equality of path-component
classes, so endpoint changes are retained.  The main iff has both directions.
Finally, the second helper expands the exact membership condition defining
`W_eq` at every strict fiber, including empty fibers.  No completeness,
nonemptiness, endpoint equality, or extra model-category hypothesis was added,
and no clause of the node was dropped.

## New nodes

None.

## Dependency modules

None; all recorded statement dependencies have usable declarations, and the
additional Segal infrastructure is an existing landed project module reused by
name.

## Second reading by Q17

I independently opened the node, its Rezk source (Sections 4.1, 5.1--5.8 and
(6.3), printed pp. 11--14), the three statement dependencies, and the complete
`SegalCategoricalEquivalence` module. The node's objects and clauses, with the
Lean rendering and verdict, are:

* The ambient object is a small simplicial space
  `W : SimplexCategoryᵒᵖ ⥤ SSet`, rendered by `SSet.Segal.Space`; the source
  assumptions are Reedy fibrancy and weak-equivalence spine maps for every
  `n ≥ 2`, rendered together by `IsSegal W`. Verdict: exact, with the same
  small-simplicial-set and Kan-complex conventions and no completeness hypothesis.
* Vertices `x,y ∈ W₀` are the explicit terms
  `(W.obj (op ⦋0⦌)) _⦋0⦌`; the strict fiber
  `M_W(x,y) = fib (d₁,d₀)` is `mappingFiber W x y`. Verdict: exact, including
  empty fibers and without an added nonemptiness assumption.
* The category has objects `x`, hom sets `π₀ M_W(x,y)`, identities represented
  by `s₀x`, and composition obtained from a degree-two lift and `d₁`; these are
  the existing `homotopyCategory` and `homotopyCategory_homs` declarations.
  Verdict: exact; no private category or composition was introduced.
* Every map of Segal spaces induces a functor on objects and mapping spaces;
  `homotopyFunctor` is the recorded construction and
  `homotopyFunctor_map_fiberEdge` gives its representative formula. Verdict:
  exact, with both Segal hypotheses present and no stronger map assumption.
* For arrows `g,g'` in `W₁` with equal component classes, the conclusion is
  `IsIso (edgeClass W g) ↔ IsIso (edgeClass W g')`, exactly the source's
  component-invariance assertion; `homotopy_category_components` has the same
  quantifier order and permits different endpoints. Verdict: exact, both
  directions retained.
* The consequence defining `W_eq` is rendered by the existing
  `equivalenceSubcomplex`; `equivalenceSubcomplex_mappingFiber` states its
  strict-fiber description in every inner degree, with the vertexwise
  isomorphism criterion. Verdict: exact, including degree zero and empty
  mapping fibers.

The source's edge cases are covered: `n = 2` is included by `2 ≤ n`; the empty
space and empty fibers are allowed; identities and constant arrows are included;
component equality may change both endpoints; and no characteristic, universe
restriction, completeness, or endpoint equality was added. The dependency
interfaces match their uses: `Enhanced.IsWeakHomotopyEquivalence` comes from
`def-cbc-enhanced-diagrams-cones`, Kan fibrancy and right properness from
`KanQuillenRightProper`, and `HomotopicalAlgebra.Reedy.matchingFrom` from
`ReedyModelStructure`.

I reran the existing-definition searches independently: `msearch.py` LeanFinder,
Loogle, and grep searches found only strict-Segal or truncated simplicial-set
results; `rg` over Mathlib, `WeilConjectures/`, and project `lean/Sheaf/` found no
matching component-invariance or strict-fiber theorem. The existing
`SegalCategoricalEquivalence` declarations are the single definitions of every
reused notion. No new node or dependency repair is needed. No mismatch was
found, so no Lean or node statement was changed. The module recompiles with
`scompile.py` (sorry diagnostics only).

Further signature checks: Mathlib's `SSet.Truncated.HomotopyCategory.homMk_id`
and `homMk_comp_homMk` give exactly the degeneracy identity and triangle
composition relations used by `homotopyCategory`; `hoFunctor.obj.equiv` confirms
that its objects are the original vertices. `π₀.mk_eq_mk_iff` is the equivalence
relation generated by edges, and `kan_realization_serre` supplies the comparison
with realized path components. The vertex quantifier in
`equivalenceSubcomplex_mappingFiber` expands the recorded `fullSubcomplex` and
uses the constant-endpoint equations of `mappingFiberSubcomplex` in every degree.
All three postponed theorems render clauses of this same node; no extra
mathematical result or definition has been introduced. The signature printed by
`tools/stage2_delivery.py signature` equals the saved `lean.statement` verbatim.
Comparison with the current shared node shows that only `lean` differs, with no
`statement_change`; there is no maintenance repair note for this item.

Additional independent searches used different wording from the first worker:
LeanFinder, "Invertible arrows in the category of a bisimplicial Segal object
form a union of connected components of its space of arrows", returned strict
Segal simplicial-set constructions, which have bijective spine maps and do not
state this result. The valid quoted Loogle query `"IsIso", "π₀"` returned only
`CochainComplex.isIso_homologyπ₀`, whose π₀ is a degree-zero homology projection,
not connected components. The earlier rejected project-namespace Loogle query
is not evidence of absence. Direct `rg` searches for `invertib`, `homotopy
equivalence`, `equivalence.*component`, `component.*equivalence`, `Segal`, and
`Rezk` in the project, Mathlib's simplicial-set directory, and the full upstream
`WeilConjectures` tree found the reused constructions and downstream consumers,
but no existing statement of this node's component or strict-fiber assertion.

The worker report's four-citer description included a text-only citation:
filtering actual `stmt_deps` and `proof_deps` yields three current citers
(composition-equivalences, equivalence-outer-horn, complete-segal-dk-levelwise).
This is a report clarification; no statement correction or citer audit is needed.
