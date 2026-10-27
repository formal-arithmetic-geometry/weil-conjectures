## Worker report

The module `Sheaf.Combinatorics.FiniteGraphEulerTrace` states
`FiniteGraph.euler_trace`. The copied node changes only its `lean` field; the
accepted Q103 split and both dependency lists are preserved. The inherited
stage-1 unchanged-item rejection does not apply to this stage-2 assignment: the
current queue lists stage 2, the live node has no Lean record, and there is no
released repair note for this item.

Hypotheses and clauses, matched individually:

- Finite vertex and edge sets are `(V : Type u) (E : Type v) [Finite V] [Finite E]`.
  Both universes are explicit and independent; neither set is assumed inhabited.
- A chosen orientation is `(s t : E → V)`, and distinct endpoints are
  `(_hne : ∀ e : E, s e ≠ t e)`. There is no injectivity assumption on endpoint
  pairs, so distinct edge indices with identical endpoints remain distinct.
- The rational spaces with bases E and V are `E →₀ ℚ` and `V →₀ ℚ`. Since the
  index sets are finite these are exactly the stated finite free vector spaces.
- `FiniteGraph.boundary s t` is the actual linear extension of
  `Finsupp.single (t e) 1 - Finsupp.single (s e) 1`. The cycle space is exactly
  `LinearMap.ker (boundary s t)`.
- Components are `Quot (fun x y : V ↦ ∃ e : E, s e = x ∧ t e = y)`.
  `Quot` identifies precisely the equivalence closure of this relation; it is not
  the quotient by the raw, nontransitive relation. Its natural cardinal is c.
- `(σV : Equiv.Perm V) (σE : Equiv.Perm E)` are the two permutations. `hσ` gives,
  for every edge, exactly the orientation-preserving or orientation-reversing
  endpoint equation. These cases cover preservation of the unordered endpoints.
- `signedEdgeMap` is the actual linear extension of the signed basis permutation:
  coefficient +1 when both orientation-preserving equations hold, -1 otherwise.
  Under `hσ` and distinctness the latter case is precisely orientation reversal.
- `cycleMap` is `LinearMap.restrict` of this specified edge map to the specified
  kernel. It uses the named proof-only helper `signedEdgeMap_mem_ker`, whose
  statement is the kernel-stability assertion in the node's proof step 3 and
  whose docstring gives that basis calculation. It does not select an arbitrary
  endomorphism or require a new action as a hypothesis. All helpers belong to
  this node and are listed in `lean.declarations`.
- The first equality uses `Module.finrank ℚ (LinearMap.ker (boundary s t))` and
  the cardinalities `Nat.card E`, `Nat.card V`, and `Nat.card (Quot ...)`.
  All four terms are explicitly cast to ℤ before subtraction, so subtraction
  is integer subtraction and never truncated natural subtraction.
- f₀ is the cardinal of `{x : V // σV x = x}`.
- f₊ is the cardinal of the edge subtype satisfying `σE e = e` and both
  endpoint-fixed equations. f₋ uses the fixed-edge equation and both
  endpoint-interchanged equations. Parallel edges exchanged with one another
  are not counted as fixed edges.
- f_c is the cardinal of the subtype of components C such that
  `∀ x : V, Quot.mk _ x = C → Quot.mk _ (σV x) = C`.
  This is setwise preservation: under endpoint preservation the vertex
  permutation maps each whole component to a component, and its inverse does
  likewise. It therefore permutes components. The displayed inclusion condition
  is exactly equality with C (not pointwise fixation of its vertices).
- The second equality is `f₀ - f₊ + f₋ = f_c - LinearMap.trace ℚ _ (cycleMap ...)`,
  with all counts explicitly cast to ℚ. `LinearMap.trace` is the recorded trace
  declaration and hence the diagonal-sum trace. The vertex permutation operator
  is implicit in the count of fixed vertices; it need not be separately bound
  to express either displayed formula.
- There are no connectedness, degree, or trivial-action hypotheses. Both
  formulas are combined by `∧`, exactly as in the node.

The source is Deligne–Mumford, graph argument after Lemma 1.17, printed p.87,
last paragraph. I opened the primary Numdam PDF and read printed pp.86–87,
including its loopless graph construction, first Betti number and Lefschetz
calculation. The local PDF is absent as already recorded by Q103; the statement
and proof preserve the node's general graph-chain expansion of that calculation.
No statement correction or statement dispute is needed.

Dependency declarations read and used:

- `def-weil-endomorphism-trace`: `LinearMap.trace` and its docstring in
  `Mathlib.LinearAlgebra.Trace`; `trace_eq_matrix_trace` identifies this with the
  sum of diagonal matrix entries. This dependency is a Mathlib leaf and needs
  no repaired Lean record.
- `def-weil-vector-space-dimension`: `Module.finrank` and its docstring in
  `Mathlib.LinearAlgebra.Dimension.Finrank`, publicly available through Trace.
- Proof dependency `def-weil-finite-dimensional-subspace`: `FiniteDimensional`
  in `Mathlib.LinearAlgebra.FiniteDimensional.Defs`.
- Proof dependency `lem-trf-vector-space-quotient-dimension`:
  `Submodule.finrank_quotient_add_finrank` in
  `Mathlib.LinearAlgebra.Dimension.RankNullity`, together with the subspace and
  quotient finiteness instances indicated in that node's Mathlib match.
- Proof dependency `lem-pc-finite-dimensional-trace-exact`:
  `LinearMap.trace_eq_add_of_exact` in
  `WeilConjectures.RingTheory.TateResidue.FinitePotent`. I read its full
  signature: three finite-dimensional spaces, injectivity, surjectivity,
  exactness and the two intertwining identities give ordinary trace additivity.
  Proof-only modules are imported without `public`.

No private replacement of trace, dimension, the free rational module, or linear
restriction is introduced. The boundary, signed edge map and cycle restriction
are the objects explicitly introduced by this same node, with real data. Their
one postponed preservation proof is precisely the node's existing step 3, not
an independent missing mathematical input. Every theorem has `sorry`; every
definition has actual data. The two postponed named theorems are
`FiniteGraph.signedEdgeMap_mem_ker` and `FiniteGraph.euler_trace`, with source and
complete natural-language proofs in their docstrings.

Edge cases checked before writing:

- Empty V forces E empty; its quotient and all counted subtypes are empty and
  its cycle space is zero, giving both equalities 0 = 0.
- Isolated vertices with arbitrary permutations have zero cycle space and
  components identical to vertices; f₀ = f_c.
- One edge with swapped endpoints has f₋ = 1, f₀ = f₊ = 0, f_c = 1, Z₁ = 0.
- Two parallel edges exchanged while vertices stay fixed have a one-dimensional
  cycle space with action -1: the second equality is 2 = 1 - (-1).
- Triangle rotation has no fixed vertices or edges, one preserved component and
  cycle trace 1; triangle reflection has f₀ = f₋ = 1 and cycle trace -1.
- Exchanging disconnected components does not count them in f_c. No hypothesis
  prevents this action. The identity action gives the dimension identity with
  true integer subtraction even for a tree or isolated vertices.

Searches made in this worker session (all msearch queries are retained in the
sandbox's searches.jsonl):

- LeanFinder: `Finite multigraph rational cycle space dimension edges minus
  vertices plus components and signed automorphism trace`. Eight results,
  including `SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`
  and real Laplacian bases. These concern simple-graph real Laplacians, not the
  rational multigraph incidence kernel or signed action formula.
- Loogle: `LinearMap.trace, LinearMap.ker`. Three results, all trace facts about
  projections/idempotents, not this graph theorem.
- Mathlib grep: `(graph|multigraph).*(homology|betti|euler|trace)|hopf.*trace|trace.*hopf`.
  Seven results, all SimpleGraph Eulerian-walk declarations; no exact match.
- LeanSearch: `Euler dimension and equivariant trace identities on the rational
  cycles of a finite multigraph`. Eight results, including the simple-graph
  Laplacian kernel formula, trace conjugacy and trace of identity. None is this
  theorem; the trace and dimension APIs are reused.
- Project rg over `lean/WeilConjectures` and `lean/Sheaf` for graph boundary,
  cycle, homology, trace and finiteGraph patterns found
  `Sheaf.Combinatorics.FiniteGraphHomologyRigidity`. I read its whole statement:
  it is integral-cycle rigidity with degree and identity-action assumptions,
  not this rational dimension/trace theorem. I reused its endpoint-map and
  Finsupp chain conventions. Grepping the exact item id in WeilConjectures gave
  no match. No existing graph boundary, signed map or restriction declaration
  was found that supplies these objects independently.
- Whole DAG concept search for graph components, graph chains, cycle spaces and
  finite multigraphs found this item and its rigidity parent, not a separate
  node defining its chain operators. Direct Mathlib source searches supplied
  `Finsupp.linearCombination`, `LinearMap.restrict`, `Quot`, `Nat.card`, trace,
  finrank and the recorded proof interfaces.

Validation on 2026-10-23: the prescribed `scompile.py` compiled the final module
both as a sandbox file and under its library module name, with no errors or
warnings. The prescribed `deliver2.py --no-push` then reported
`OK (dry run): commit 6d7e536f521 passes the preflight and compiles; nothing pushed`.
The inherited unchanged-item refusal did not recur. The final file has explicit
universes, `autoImplicit false`, module mode, appropriate public/proof imports,
and no line exceeding 100 characters. The node differs from the current read
clone only in `lean`; the signature matches the declaration verbatim, excluding
the defining delimiter as required by preflight. No mathematical repair was
needed on this retry.

## Second reading by Q45

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
