## Worker report

The module `Sheaf.Algebra.Lie.ArbitraryBasisPBW` states
`UniversalEnvelopingAlgebra.exists_arbitrary_basis_pbw`. Its only proof is `sorry`.
It introduces no definitions, helper nodes, or replacement dependency interfaces.
The item changes only in `lean`; its accepted stage-1 split is preserved.

The inherited BLOCKED ending concerns the already reviewed stage-1 split, not this
stage-2 assignment. The current `coord/queue.tsv` lists the item at stage 2, the
node has no Lean record, and there is no repair note. The handoff rule in
`coord/brief-stage2.md` section 0 therefore applies.

Source checked directly: `literature/milne-algebraic-groups_iAG2017.pdf`, PDF
pages 211–216, printed pages 199–204. Theorem 10.36 on printed page 200 uses an
arbitrary index set I; footnote 2 specifies that ordered means totally ordered.
The preceding paragraphs construct the tensor quotient and degree-one map.
The docstring records all seven steps of the accepted DAG proof, including its
length/inversion rank and compatibility modulo smaller relations. No assertion
from the flawed printed reduction-on-sums argument is silently used.

Hypotheses and clauses, in order:

- A rational Lie algebra is `(L : Type u) [LieRing L] [LieAlgebra ℚ L]`.
  There is no dimension, finite-generation, nonzero, or cardinality hypothesis.
- The tensor quotient U(L) is `UniversalEnvelopingAlgebra ℚ L`. Its `Rel`,
  `ringCon`, and quotient definition were read in Mathlib. The relation is
  `ιₜ ⁅x,y⁆ + ιₜ y * ιₜ x = ιₜ x * ιₜ y`, exactly the node's ideal relation.
- The canonical map j is `UniversalEnvelopingAlgebra.ι ℚ`. Its definition is the
  quotient map composed with `TensorAlgebra.ι ℚ`; its underlying function and
  linear map are used, without introducing an arbitrary map.
- Every basis and every total order are quantified by
  `∀ (B : Type v) [LinearOrder B] (e : Module.Basis B ℚ L)`.
  The universe v is explicit and independent of u. Neither a finite alphabet
  nor a well-founded order is required.
- Finite nondecreasing lists are the subtype
  `{w : List B // w.Pairwise (fun a b : B ↦ a ≤ b)}`. Pairwise nonstrict
  comparison says exactly that all earlier letters are at most later ones.
  Repeated letters and lists of every finite length are included.
- The required rational vector-space basis is the existential `E : Module.Basis`
  on that subtype. Its value at every index is explicitly
  `(w.val.map (fun b ↦ ι ℚ (e b))).prod`. `List.prod` keeps the original
  order in this potentially noncommutative algebra. In particular, its value
  at the empty list is one, by the definition of the empty product.
- Injectivity is the separate conjunct
  `Function.Injective (ι ℚ : L → UniversalEnvelopingAlgebra ℚ L)`.
  This conjunct does not require a supplied basis or an ordered index set.
- The zero Lie algebra is `Subsingleton L` (an additive group has a zero).
  Under this hypothesis the first conjunct gives `IsEmpty B`, so the only
  list index is the empty list and the sole basis vector is one. The final
  conjunct gives `Function.Bijective (algebraMap ℚ (UniversalEnvelopingAlgebra ℚ L))`.
  Bijectivity of this canonical rational algebra map expresses U(0) = ℚ as
  an algebra identification, including its scalar compatibility; it does not
  assert literal equality between different Lean carrier types.

Dependency declarations used:

- `def-wf-lie-algebra`: `LieRing` and `LieAlgebra`,
  `Mathlib.Algebra.Lie.Basic`, publicly available through the enveloping module.
  Their complete class signatures, including alternation, Leibniz/Jacobi, and
  scalar compatibility, were read. The node's other examples and notions are
  irrelevant to this statement.
- `lem-sfb-enveloping-universal-property`:
  `Mathlib.Algebra.Lie.UniversalEnveloping`, `UniversalEnvelopingAlgebra`,
  `UniversalEnvelopingAlgebra.ι`, and the recorded `lift`, `lift_ι_apply`,
  `lift_unique`. Their complete signatures and construction were read. The
  statement uses exactly that algebra and map; the universal-property theorems
  justify the existing dependency match, rather than being extra hypotheses.
- Proof import `Mathlib.LinearAlgebra.TensorAlgebra.Basis` provides
  `Module.Basis.tensorAlgebra` and `TensorAlgebra.equivFreeAlgebra` from
  `lem-sfb-tensor-word-basis`; the full signatures and docstrings were read.
- Proof import `Mathlib.LinearAlgebra.Basis.VectorSpace` provides
  `Module.Free.of_divisionRing` from `lem-weil-pbc-vector-space-free`; its
  signature and construction through `Basis.ofVectorSpace` were read.
- `lem-sfb-triangular-linear-relations` currently has no Lean record or
  Mathlib match. It is a proof dependency, not a missing notion needed to type
  this statement. Its proof-plan citation remains in the docstring; there is
  no module to import at this stage. The maintainer can add its proof import
  when that node is stated, as required by stages/2-statements.md section 3.7.

Edge cases checked before writing:

- Zero L and empty B: the only finite list is empty, its product is one,
  and the canonical scalar map is an isomorphism. No contradictory assumption
  `Nontrivial L` or `Nonempty B` appears.
- Empty and singleton words: pairwise comparison is vacuous; singleton words
  are exactly the generator images used for the injectivity consequence.
- Repeated indices are permitted by ≤; the theorem includes all powers.
- Infinite bases and orders such as the usual order on ℤ are allowed.
  The reduction proof uses the rank in ℕ², not well-foundedness of B.
- The injectivity and scalar-map conjuncts remain meaningful independently
  of the universe chosen for B. No universal quantification over too-small
  test objects is used to assert injectivity.
- The construction does not assume commutativity of U(L). For abelian L it
  specializes to the usual monomial basis of its symmetric algebra.

Searches for an existing declaration (2026-10-24):

- `msearch.py ... leanfinder`, query:
  "For an arbitrary dimensional rational Lie algebra ordered products of any
  totally ordered vector space basis give a basis of the universal enveloping algebra".
  Eight hits: the enveloping algebra construction and relation, its inhabited
  instance, and Geck-construction Lie algebras. None is PBW or canonical-map
  injectivity.
- `msearch.py ... leansearch`, query:
  "Poincare Birkhoff Witt theorem arbitrary dimension ordered monomial basis
  universal enveloping algebra injectivity canonical map". Eight hits:
  `ι`, `ι_apply`, `lift`, `lift_unique`, `mkAlgHom`,
  `Module.Basis.symmetricAlgebra`, and monomial-order constructor lemmas.
  The symmetric-algebra basis concerns a different algebra; none supplies PBW.
- `msearch.py ... loogle`, query:
  `UniversalEnvelopingAlgebra, Module.Basis`. Successful search, zero hits.
- `msearch.py ... grep`, query `Poincar|Birkhoff|PBW|pbw|ι_injective`,
  subdirectory `Algebra/Lie`. Three hits, all comments in `Free.lean` and
  `SerreConstruction.lean` saying their alternative arguments need PBW.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for
  `Poincar|Birkhoff|\bPBW\b|\bpbw\b|ordered.*[Bb]asis|pbwBasis`, plus the
  exact node id in `lean/WeilConjectures`. No arbitrary-dimensional PBW
  declaration or exact node-id hit was found. The existing
  `Sheaf.Algebra.Lie.FieldFilteredPBW` was opened in full: its theorem
  `exists_field_filtered_pbw_basis` requires `e : Module.Basis (Fin n) F L`
  and therefore cannot state this node. Integral Kostant PBW concerns a
  different algebra and finite root data.
- Exact-name `rg` for `exists_arbitrary_basis_pbw` in the project and Mathlib
  found no declaration before this file was written.

No statement correction, dependency repair, or disputed mathematical claim is
needed. All variables and universes are explicitly bound. The expected single
`sorry` belongs to the theorem matching this DAG node.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
