## Worker report

Stage 2 delivery of `lem-sfb-cubical-partition-boundary-expansion`. The accepted
stage-1 split is unchanged. The previous ending concerned a stage-1 unchanged-item
refusal; the current `coord/brief-stage2.md` §0 explicitly permits this stage-2
handoff. No Lean work was preserved in the sandbox.

The module states `IntegralLatticeCubical.partitionBoundaryExpansion`, with the
whole proof `sorry`, and constructs the two individual face contributions by
explicit finite cubical formulas. All definition data is real. No definition of
chains, tensor products, partition sums or signs is duplicated. No statement
correction, disputed statement, new node, or dependency-record repair is needed.

Clause-by-clause correspondence:

- `r : ℕ` is every integer rank at least zero, including zero; `v : Fin r → ℤ`
  is an arbitrary lattice point in D. `I : Finset (Fin r)` is the arbitrary
  ordered direction subset, using zero-based finite indexing with the same order.
- The published `Directions r a`, `Chains r a`, `cell`, `unitVector`, and
  `boundary` give exactly the existing free abelian groups C_a, their basis,
  standard vectors and signed cubical differential. Integer degrees are retained
  there and groups outside 0 through r have empty bases. In the present formulas
  only nonnegative degrees occur, so the already published ℕ-indexed zero extension
  is used. At total degree zero, `d 0 0` is zero; natural subtraction in
  `I.card - 1` therefore also covers the empty case without excluding it.
- `directionSum` is u_A; `partitionSign` is epsilon(A,C), counting precisely
  the pairs with second coordinate less than first. `diagonalComponent r I.card
  (cell r (I.card : ℤ) v I)` is P(v,I), the finite signed ordered partition sum.
  `tensorCell` includes each pure tensor into Mathlib's graded total tensor group.
  The actual `HomologicalComplex.tensorObj ... .d` is d_T, with the Koszul sign
  on the second factor; it is not a freely chosen or assumed map.
- The first conjunct quantifies over every `i`, `B`, `C`, with hypotheses
  `i ∈ I`, `Disjoint B C`, and `B ∪ C = I.erase i`. These are exactly the
  hypotheses in the node; in particular i is absent from both B and C.
- In that conjunct, filtered cardinalities of B below i, C below i, B above i,
  and filtered `B.product C` are p, q, t, and N. The first equality identifies
  the actual first-face coefficient `partitionSign (insert i B) C * (-1)^position`
  with `(-1)^(N+q+p)`, and the second identifies it with the displayed s.
  The third identifies the actual second-face coefficient (including `(-1)^B.card`)
  with `(-1)^(N+t+|B|+q)`, and the fourth identifies that with s.
- The fifth and sixth equalities identify `partitionFirstFace` and
  `partitionSecondFace` with the two differences in the node, with exactly the
  stated vertices, directions, and common coefficient s. Their definitions select
  a face of the given cubical boundary and its unchanged tensor partner, multiplying
  by the actual shuffle, position, and second-factor Koszul signs.
- The two `Set.BijOn` conjuncts are the first- and second-face indexing bijections.
  Source indices are `(A,C,i)` with disjoint union I and i in the applicable part;
  target indices are `(i,B,C)` with disjoint union `I.erase i`. Their actual maps
  erase i from the first or second part, respectively. The explicit inverses by
  insertion are given in the theorem's proof docstring, not assumed as extra data.
- The next conjunct is the exact final boundary expansion. The outer sum is over
  `i ∈ I`; `B ∈ (I.erase i).powerset` enumerates each ordered disjoint partition
  once, with `C = I.erase i \ B`. Its coefficient is
  `(-1)^(I.filter (fun j ↦ j < i)).card * partitionSign r B C`.
  The two outer tensors use `[v+u_i,B] ⊗ [v+u_i+u_B,C]` and
  `[v,B] ⊗ [v+u_B,C]` as stated, in degree `I.card - 1`.
- The last conjunct explicitly states vanishing for `I = ∅`; the expansion's RHS
  is then the empty sum, so this is the node's required 0=0 case.

Dependency declarations read and used:

- `Sheaf.AlgebraicTopology.IntegralLatticeCubicalContraction`:
  `IntegralLatticeCubical.Directions`, `Chains`, `cell`, `unitVector`, `boundary`,
  `incomingBoundary`, `contraction`; signatures, construction and proof docstrings read.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free` is the existing
  free-module notion, with `Finsupp` as the actual free group in the construction.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, `.Map`:
  `TensorProduct`, `TensorProduct.mk`, `TensorProduct.lift`, `LinearMap.rTensor`;
  their definitions and universal-property / pure-tensor signatures were read.
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`:
  `HomologicalComplex.homology`, with `ChainComplex` and homological-complex morphisms
  as in the dependency's mathlib_match. Homology itself is background terminology,
  not an extra vanishing claim of this node.
- Existing helpers in `Sheaf.AlgebraicTopology.IntegralCubicalChainDiagonal`:
  `IntegralLatticeCubical.chainComplex`, `directionSum`, `partitionSign`,
  `tensorCell`, `diagonalComponent`. Their full definitions and docstrings were read.
  The module is publicly imported to reuse these constructions; its theorem
  `IntegralLatticeCubical.diagonal` is not used. The four recorded dependency
  modules are available through this public import and its public import closure.

Import-cycle exception under stages/2-statements.md §3 rule 7: the existing
`lem-sfb-integral-cubical-chain-diagonal` cites this item as a proof dependency.
Its module must NOT import this new module, since the new statement reuses its
published construction helpers. That reverse proof import would close an import
cycle. The parent is not added as a DAG dependency (which would likewise create
a cycle); only its existing construction declarations are used here. A future
maintainer reorganization can separate those constructions from its theorem.

Edge checks: before writing, inspected empty I, rank zero, singletons, either
partition part empty, first/last coordinate, and top degree. A finite independent
integer calculation verified both sign formulas, the two face reindexings and
the complete boundary expansion for all 31 subsets in ranks 0–4. Coordinates
may be arbitrary integers: the calculation uses only formal translations, so no
positivity of coordinates is assumed. Both unpaired middle tensors match literally
and have opposite coefficients. No counterexample or missing hypothesis was found.

Searches for exact existing statements:

- `msearch.py` LeanFinder: "Signed cubical lattice partition tensor boundary
  expansion cancellation of paired faces"; eight hits on box-integral boundaries,
  topological cubes and ordered partitions, none the algebraic statement.
- `msearch.py` LeanSearch: "cubical chain diagonal boundary signed partitions";
  eight hits including `Cube.boundary`, `Rep.standardComplex.d_of` and total-complex
  sign APIs. None states this partition expansion or its paired face bijections.
- `msearch.py` Loogle: `TensorProduct.map, Finset.powerset, Finset.BijOn`;
  no hits, with unknown identifier `Finset.BijOn`. The statement correctly uses
  the actual set-function notion `Set.BijOn` instead.
- `msearch.py` Mathlib grep: `partitionSign|partitionBoundary|cubical.*boundary|cubical.*partition`;
  zero hits. Direct `rg` of the project `lean/Sheaf` and `lean/WeilConjectures`
  for cubical names found the two cited existing construction modules, not this
  detailed statement. Exact-ID grep in `lean/WeilConjectures` found no match;
  searches for `partitionBoundary`, `partition_boundary`, and this new module's
  name found no existing statement. Thus the parent theorem is not an exact
  substitute: it does not assert the individual signs, paired faces or bijections.

Source check: opened current `literature/blueprint/latest/.../` direct-images proof,
paragraph (3). As the node explicitly records, it is the route location only;
the six-step agent-written DAG calculation is the actual statement/proof source.
The new theorem docstring carries all six proof steps and dependency citations.

Validation: `scompile.py Q58 lem-sfb-cubical-partition-boundary-expansion` compiled
this file separately in both sandbox and library module naming contexts, with
no error and no unexpected warning (6.2s and 7.5s in the initial run).

## Second reading by Q58

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
