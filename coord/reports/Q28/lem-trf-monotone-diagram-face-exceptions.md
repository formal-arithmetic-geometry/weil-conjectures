## Worker report

The module `Sheaf.RingTheory.MonotoneDiagramFaceExceptions` states
`MonomialDiagram.faceExceptions_subset_box_and_finite`, with its proof `sorry`.
It supplies three concrete helpers belonging to this node: `region` packages the
complement and the existing quotient supports; `vertexDegreeBound` computes M;
`faceExceptions` is the displayed exceptional set. There are no additional
postponed theorems or hollow definitions.

Hypothesis and clause correspondence:

- `n s : ℕ` and `hn : 1 ≤ n` are the dimension, number of vertices, and positive
  dimension hypothesis. Exponents use `Fin n →₀ ℕ`, exactly the exponents of
  `MvPolynomial (Fin n) ℤ`. Since the variable set is finite this includes every
  vector in ℕⁿ. Coordinates and vertex indices are zero-based.
- `D : Set (Fin n →₀ ℕ)` is the diagram. `hD : IsMonotone D` unfolds to the two
  assumptions in the node: additive closure, and closure under
  `a - Finsupp.single p (a p) + Finsupp.single t (a p)` whenever `p < t`.
  This moves the entire p coordinate, not just a single unit.
- `α : Fin s → Fin n →₀ ℕ` is the finite list. `hα : IsOrderedVertexFamily D α`
  says that its range is exactly the coordinatewise minimal elements and that
  earlier indices have strictly smaller `Finsupp.DegLex` exponents.
  Read Mathlib's definitions: this compares `(degree, exponent)` by `Prod.Lex`,
  then uses `Finsupp.Lex = Pi.Lex`. Thus it is the ascending order
  `(∑ α_j, α_1, …, α_n)` required by the node, not a reverse lexicographic order.
- `region D α none = Dᶜ` renders Δ₀. `region D α (some i) = quotientSupport α i`
  renders Δᵢ₊₁. The existing support is
  `{β | ∀ h, h < i → ¬ α h ≤ α i + β}`. For natural exponent vectors,
  `α h ≤ α i + β` is equivalent to membership of `α i + β` in the translated
  orthant `α h + ℕⁿ`, so this is exactly the displayed region.
- `vertexDegreeBound α = max 1 (Finset.univ.sup fun i ↦ (α i).degree)` is the
  specified maximum. `Finsupp.degree_eq_sum` identifies degree with the sum of
  all n coordinates. The empty supremum is zero, hence M=1 for an empty list.
- `i : Option (Fin s)` quantifies over all s+1 regions, including the complement;
  `r : Fin n` means `0 ≤ r < n`. In zero-based coordinates the face condition
  `∀ j, j < r → β j = 0` fixes the first r coordinates. `Finsupp.single r 1`
  is the node's one-based vector e_(r+1).
- `faceExceptions` requires membership in the region, the face condition, and
  failure of membership after adding precisely that coordinate vector.
- The first conclusion is inclusion in the box with the same face condition
  and `∀ j, r ≤ j → β j < vertexDegreeBound α`. The second conjunct states
  finiteness of that exact exception set. Neither clause has been dropped.

Dependencies used:

- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, the polynomial-ring
  dependency. Its signature/docstring and the recorded `MvPolynomial.aeval`
  and `MvPolynomial.algHom_ext` signatures/docstrings were read; no polynomial
  universal-property lemma is required for this exponent-only statement.
- `Sheaf.RingTheory.SupportedHomogeneousDivision`:
  `MonomialDiagram.IsMonotone`, `MonomialDiagram.IsOrderedVertexFamily`, and
  `MonomialDiagram.quotientSupport`. The owning already-landed definition node
  `def-trf-supported-homogeneous-division` is added to `stmt_deps`, as authorized
  for a landed notion. Its record is usable unchanged. The import also exposes
  the existing exponent-degree API and the polynomial-ring dependency.
- `Mathlib.Data.Finset.Lattice.Fold`: `Finset.sup` computes the finite maximum.

The module docstring and theorem docstring identify the agent quantitative
refinement and carry all seven elementary proof steps from the DAG. I opened
[Bierstone--Milman 1997, pp. 274–275](https://mahalex.net/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf),
Lemma 8.2 and Remarks 8.4: these provide the qualitative region and coordinate
translation context; the precise M-box strengthening is the agent refinement
explicitly identified in this node. The definition-module source and full
signatures were read. The prescribed old `CompactObject` example is withdrawn
in `lean/Sheaf`; I also read its recorded upstream module for current conventions.

Edge cases checked before finalizing:

- D empty forces s=0; the sole region is all exponent vectors and its exception
  sets are empty; M=1.
- D full has the unique minimal vertex 0 and s=1; the vertex region is full and
  the complementary region empty, so both exception sets are empty; M=1.
- s=0 is supported by `Option (Fin 0)` and empty `Finset.univ.sup` without any
  choice of a nonexistent vertex. The first vertex has no earlier vertices.
- n=1 and r=n−1 require only the last-coordinate bound, with no later
  coordinates. r=0 imposes no zero-coordinate restriction. No nonempty-index,
  nonzero-vertex, or proper-diagram hypothesis was added.
- An executable finite check enumerated all antichains of up to three vertices
  of degree at most three in dimensions 1, 2, and 3, retaining exactly those
  whose generated diagrams satisfy whole-coordinate monotonicity. This checked
  5, 21, and 43 diagrams respectively, every region and every face, and all face
  vectors with coordinates through M+1. Every exceptional vector satisfied the
  stated strict box bound. This is an edge check, not a Lean proof.

Searches actually run (using the prescribed msearch.py wrapper):

- LeanFinder: “Ordered minimal vertices of an additive monotone subset of natural
  exponent vectors have finitely many exceptions to coordinate translation on
  faces”. Eight hits, including Nobeling good products, admissible box indices,
  Behrend boxes, antidiagonals, and formal multilinear-series indices. Returned
  signatures do not state this exceptional-set bound.
- Loogle: `Pi.Lex, Minimal, Set.Finite`. Zero hits.
- Mathlib grep in RingTheory:
  `monotone.?diagram|exceptional.?translation|Pommaret|Janet`. Zero hits.
- LeanSearch: “A monotone upward closed monomial exponent diagram with vertices
  sorted by degree lexicographic order has finite coordinate face translation
  exceptions bounded by the maximum vertex degree”. Eight hits on `DegLex`,
  `MonomialOrder.degLex`, and degree monotonicity; none is the exception theorem.
- Local rg in `lean/WeilConjectures` and `lean/Sheaf` for diagram/exceptional
  translation/Pommaret/Janet initially found a source citation. The subsequent
  search for `namespace MonomialDiagram`, `faceExceptions`, and
  `vertexDegreeBound` found the landed supported-division and stabilization
  modules; I read them and reused their notions. No existing exception theorem,
  region package, or bound helper was found. The node-ID grep in
  `lean/WeilConjectures` and upstream-name search gave no attachment.

No statement correction, disputed statement, new node, or dependency repair is
needed. Only `lean` and the authorized addition of the landed definition node to
`stmt_deps` change in the item. All writes are confined to the assigned sandbox.
Compilation and delivery validation use only scompile.py and deliver2.py.
The maintainer supplies the independent reading under the direct-worker rule.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
