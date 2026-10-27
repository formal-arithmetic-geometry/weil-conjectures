## Worker report

The module `Sheaf.Combinatorics.FiniteGraphHomologyRigidity` states
`finiteGraphHomologyRigidity`, with its proof exactly `sorry`. It includes the
finite-rank freeness assertion as the first conjunct and the rigidity assertion
as the second conjunct. No definitions, auxiliary axioms, or proved lemmas are
introduced. Only the item's `lean` field changes; its accepted stage-1 split,
statement and all dependency lists are preserved.

The inherited BLOCKED concerned the prohibition on re-splitting a reviewed
stage-1 node. The current `coord/brief-stage2.md` §0 expressly distinguishes
stage-2 handoff from re-splitting. This item currently has no Lean record and
`coord/queue.tsv` lists it at stage 2. No repair note for this item is present.
The sandbox initially contained only dispatcher brief marker files, so no
interrupted delivery or source mutation was repeated.

Clause-by-clause rendering:

- Finite vertex and edge sets: explicitly bound `V : Type u`, `E : Type v`,
  `[Finite V]` and `[Fintype E]`, with independent explicit universes `u v`.
  A finite set may always be treated as its element type. The enumeration of E
  only evaluates degree; the result is independent of its choice.
- Orientation and looplessness: `s t : E → V` and
  `_hne : ∀ e : E, s e ≠ t e`. These are exactly a choice of orientation of
  each unordered distinct endpoint pair. There is no injectivity condition on
  the pair `(s e, t e)`, so parallel edges remain distinct.
- The degree counts incident edges with multiplicity: the expression
  `(Finset.univ.filter (fun e : E ↦ s e = x ∨ t e = x)).card` counts edge
  indices incident to x. Looplessness means each edge contributes once at each
  endpoint; distinct parallel edges contribute separately.
- The free abelian groups on E and V are `E →₀ ℤ` and `V →₀ ℤ`. Since these
  index types are finite they are canonically the groups of all functions
  used by the node, without any extra support restriction in mathematical
  content. The standard generator e is `Finsupp.single e 1`.
- The boundary is `Finsupp.linearCombination ℤ (fun e : E ↦
  Finsupp.single (t e) (1 : ℤ) - Finsupp.single (s e) 1)`.
  It takes each generator to precisely t(e)-s(e). `LinearMap.ker` of this
  displayed boundary is the cycle lattice. Its freeness of finite rank is
  `∃ r : ℕ, Nonempty (Module.Basis (Fin r) ℤ (LinearMap.ker ...))`.
- An automorphism is quantified as `σV : Equiv.Perm V` and
  `σE : Equiv.Perm E`. Endpoint preservation is the disjunction, for every e,
  of preserving the two ordered endpoints and interchanging them. Thus this
  does not require preservation of the arbitrarily chosen orientation.
- The signed edge action is the linear combination taking e to
  `Finsupp.single (σE e) 1` if `σV (s e) = s (σE e)` and to its negative
  otherwise. By endpoint preservation and distinct endpoints these are
  exactly the preserved-orientation and reversed-orientation cases.
  This is the specified canonical action, not an unconstrained map parameter.
- Fixing all vertices of degree at most two is the hypothesis
  `∀ x : V, (...) .card ≤ 2 → σV x = x`.
- Identity on H₁ is `∀ c : E →₀ ℤ, boundary c = 0 → signedAction c = c`.
  This states equality on every element of the kernel, equivalently identity
  of the restricted map; it neither asks for identity on all edge chains nor
  merely asks for invariance of the kernel. Endpoint preservation already
  ensures that the signed action preserves the kernel.
- Fixing every vertex and every edge is the conjunction
  `σV = Equiv.refl V ∧ σE = Equiv.refl E`.
- There is no connectedness, nonemptiness, positive-rank, or lower-degree
  assumption. `[DecidableEq V]` permits the concrete coefficient formula and
  is available classically for every V; no decidable equality on E is assumed.

Dependency declarations read and used:

- The sole statement dependency
  `lem-weil-subgroup-finite-free-abelian-group-free` is a Mathlib leaf. Its
  `mathlib_match` is `Submodule.basisOfPid`, in
  `Mathlib.LinearAlgebra.FreeModule.PID`, whose full signature and docstring
  were read: for a finite basis b of a module over a PID and a submodule N,
  it returns `Σ n : ℕ, Module.Basis (Fin n) R N`. This module is publicly
  imported; the theorem's docstring explains its specialization to our kernel.
- `Mathlib.LinearAlgebra.Finsupp.LinearCombination` supplies the canonical
  extension `Finsupp.linearCombination`; its definition and evaluation formula
  were read. `LinearMap.ker`, `Module.Basis` and `Finsupp.single` use the
  existing Mathlib notions. `Mathlib.Data.Fintype.Perm` supplies finite-type
  permutation material.
- Proof dependency `lem-sfb-finite-graph-euler-trace` has no Lean record and is
  currently unsplit. It is needed only for the future proof, not to type this
  statement. Its exact full statement was read and its use retained in the
  proof docstring. There is no module to import for it yet.

Searches (2026-10-23):

- `msearch.py ... leanfinder "A finite loopless multigraph automorphism fixing
  vertices of degree at most two and acting trivially on integral cycle
  homology is the identity"`: 8 hits, concerning `SimpleGraph.cycleGraph`,
  `SimpleGraph.IsCycles`, identity graph maps and walks; none is this lemma.
- `msearch.py ... loogle '"Graph", "homology"'`: OK, 0 hits.
- `msearch.py ... grep
  '(graph|multigraph).*(homology|rigidity)|(homology).*(graph|multigraph)'`:
  OK, 0 hits.
- `msearch.py ... leansearch "An automorphism of a finite loopless multigraph
  fixing all degree at most two vertices and acting trivially on integer
  cycles is identity"`: 8 hits, including `SimpleGraph.Iso.degree_eq`,
  `Graph.isLink_self_iff`, graph identity isomorphisms and permutation cycle
  facts; none states cycle-lattice rigidity.
- `rg` on Mathlib's `Combinatorics/Graph` and inspection of `Graph/Basic.lean`
  found its general embedded multigraph definition, but no homology, degree
  or cycle-lattice rigidity declaration. This theorem does not introduce a
  competing graph definition: it directly quantifies the endpoint data that
  the node specifies and uses Mathlib linear algebra throughout.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for finite graph, multigraph,
  cycle lattice and homology rigidity found no existing representation or
  statement. Graphs of scheme morphisms and informal curve-tree docstrings
  are unrelated. The exact blueprint id search in `lean/WeilConjectures`
  returned no match. The proposed theorem name search on Mathlib and both
  project roots returned no match.
- DAG search for cycle lattice, loopless multigraph and integral cycles found
  this item, its Euler-trace proof input and nodal-curve consumers; none has a
  Lean definition of this notion to reuse.

Edge cases checked before writing: empty V forces E empty by looplessness;
empty E allows arbitrarily many isolated vertices, all of which the degree
hypothesis fixes. A single edge with swapped endpoints violates the degree
hypothesis even though its cycle lattice is zero. Two parallel edges swapped
with endpoints fixed negate their difference cycle, violating identity on H₁.
Swapping endpoints AND the two parallel edges can act identically on their
cycle lattice but violates the degree-two fixed-vertex hypothesis. A triangle
rotation acts identically on H₁ but also violates that hypothesis. A graph
with bridges or trees has no hidden assumption that every edge lies in a
cycle. Disconnected components are allowed, including possible component
permutations; the identity-on-cycles and low-degree hypotheses are global.
Arbitrarily reversing chosen edge orientations only conjugates the displayed
operators and introduces no additional restriction.

Source checked: the primary Numdam PDF of Deligne–Mumford, printed pp. 86–87,
https://www.numdam.org/item/PMIHES_1969__36__75_0.pdf, including the paragraph
asserting the result for any finite graph with the three properties of
Lemma 1.17 and its deletion/suppression and Lefschetz argument. This agrees
with the unchanged item. No statement fault or disputed clause was found.

Validation: the first scompile run elaborated both module modes and reported
only two removable lint warnings: unused `DecidableEq E` and a `Fintype V`
that need only be `Finite V`. The final signature removes the former and
uses `Finite V`. All compiles use the prescribed scompile.py wrapper.

## Second reading by NM

A separate reading pass by this worker checked the finished node copy against
the finished file, without delegation (the dispatcher prohibits other agents).
The independent maintainer review is still required. The kernel has the target
minus source convention in both occurrences. The action sign compares the image
of the OLD source under σV to the NEW source of σE e; it therefore detects
orientation reversal relative to the chosen orientations. The low-degree count
counts edge labels, not neighbours, so parallel edges are preserved. The free
finite-rank clause is present before quantifying automorphisms, and identity
on cycles is required only under the zero-boundary premise. Both permutations
are concluded equal to their identity equivalences. Empty and disconnected
cases remain admitted. No mismatch was found in this pass; the only changes
from compilation were the two typeclass choices documented above. The accepted
node statement and split remain byte-for-byte unchanged after JSON parsing.
