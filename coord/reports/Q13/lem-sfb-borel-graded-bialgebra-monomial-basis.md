## Worker report

The module `Sheaf.RingTheory.BorelBialgebraMonomialBasis` states
`GradedAlgebra.borel_bialgebra_monomial_basis`, with its proof `sorry`.
It defines no new notion and proves nothing. The item's node changes only in
`lean`; its statement, statement dependencies and accepted seven-step proof
are preserved. The seven proof steps are carried into the theorem docstring.

The previous worker's ending concerned a stage-1 resplitting assignment.
The current `coord/brief-stage2.md` §0 expressly distinguishes that ending
from the present stage-2 handoff. `coord/queue.tsv` lists the item in stage 2,
the current node has no Lean record, and there is no released repair note
for the item. This delivery states the accepted split without reopening it.

Source read: `literature/milne-abelian-varieties_AV.pdf`, I Lemma 12.2,
printed p.55 (PDF page 61), including the preceding algebra and coproduct
discussion. The proof's first sentence quotes Borel's structure theorem:
homogeneous generators subject only to signed commutativity and their
nilpotence relations. This item is that finite-dimensional structure input,
before the top-degree equality criterion. The already landed
`Sheaf.RingTheory.BoundedBialgebraExterior` states the subsequent equality
criterion and supplies an identical, reusable choice of input conventions;
it does not state the present theorem and is not imported.

Hypotheses, individually matched to the node:

| Node hypothesis | Lean rendering |
| --- | --- |
| A field k | `(k : Type u) [Field k]` |
| k is perfect, including characteristic zero | `[PerfectField k]` |
| A unital associative k-algebra H | `(H : Type v) [Ring H] [Algebra k H]` |
| H is finite dimensional | `[FiniteDimensional k H]` |
| 1 is not 0 | `[Nontrivial H]` together with the ring structure |
| A nonnegative direct-sum grading with graded multiplication | `(𝒜 : ℕ → Submodule k H) [GradedAlgebra 𝒜]` |
| H^0 = k·1 | `hconnected : 𝒜 0 = Submodule.span k {(1 : H)}` |
| Signed commutativity for all homogeneous a and b | `hcomm`, quantified over `i j : ℕ`, `x : 𝒜 i` and `y : 𝒜 j`, with sign `(-1 : k) ^ (i * j)` |
| The k-linear coproduct Δ and degree-zero projection ε | `(Δ : H →ₗ[k] H ⊗[k] H) (ε : H →ₗ[k] k)` |
| Δ preserves total degree | `hdegree`, membership in the span of pure tensors with `i + j = n` |
| Δ is unital | `hunit : Δ 1 = (1 : H) ⊗ₜ[k] (1 : H)` |
| Δ is multiplicative for the signed tensor product | `hmul`, applying `GradedTensorProduct.of k 𝒜 𝒜` to Δ, then using the multiplication of `GradedTensorProduct` |
| Δ is coassociative | `hcoassoc`, using `TensorProduct.assoc` to identify the two triple tensor parenthesizations |
| ε is projection to H^0 = k | `hprojection`, identifying `algebraMap k H (ε x)` with `GradedAlgebra.proj 𝒜 0 x` |
| Both counit identities | The two conjuncts of `hcounit`, using respectively `TensorProduct.lid` and `TensorProduct.rid` |

The coproduct is a linear map equipped with explicit unit and multiplication
conditions; these are exactly the data and laws of a unital k-algebra map to
the signed tensor algebra. An ordinary `Bialgebra k H` would impose the wrong
unsigned tensor multiplication. `GradedTensorProduct.tmul_coe_mul_coe_tmul`
in Mathlib's internal graded tensor product source confirms the sign from
the degree of the second factor of the first tensor and the first factor
of the second tensor. The maps `GradedTensorProduct.of` are linear
equivalences of the underlying vector spaces. Projection is specified by
`hprojection`, so ε is not an arbitrary additional map.

Conclusions, individually matched to the node:

| Node conclusion | Lean rendering |
| --- | --- |
| A nonnegative integer r | `∃ (r : ℕ)` |
| Positive integer degrees d_1,...,d_r | `(d : Fin r → ℕ)` and `∀ j, 0 < d j` |
| Homogeneous generators x_j in H^(d_j) | `(x : Fin r → H)` and `x j ∈ 𝒜 (d j)` |
| Integer heights N_j at least two | `(N : Fin r → ℕ)` and `2 ≤ N j` |
| Each specified nilpotence relation | `x j ^ N j = 0` for every j |
| Exponents 0 ≤ a_j < N_j | The index type `(j : Fin r) → Fin (N j)` |
| These ordered monomials are a k-basis of H | `∃ b : Module.Basis ((j : Fin r) → Fin (N j)) k H`, with `b a = (List.ofFn fun j : Fin r ↦ x j ^ (a j : ℕ)).prod` |
| Each monomial has degree sum a_j d_j | `b a ∈ 𝒜 (∑ j : Fin r, (a j : ℕ) * d j)` |
| For r = 0 the sole monomial is 1 | There is one function on `Fin 0`; `List.ofFn` is empty and `List.prod []` is 1 |
| No highest-degree / dim H^1 hypothesis | There is no such binder or condition in the theorem |

The list product fixes increasing `Fin r` order, which matters in a signed
commutative ring; it does not use a commutative finite product in H. Natural
numbers represent precisely the nonnegative r, positive degrees and heights
of the node; there is no mathematical restriction from using ℕ here.

Dependencies and declarations read:

- The only statement-dependency node is `def-weil-field`, status `mathlib`.
  Its `mathlib_match` is `Field`. The full class and docstring were read in
  `Mathlib.Algebra.Field.Defs`, line 180: it extends `CommRing` and
  `DivisionRing`, with inverses for nonzero elements. It is imported via
  `Mathlib.FieldTheory.Perfect`.
- `Mathlib.FieldTheory.Perfect`: `PerfectField` (line 289), its characteristic
  zero instance, `PerfectRing.toPerfectField` and
  `PerfectField.toPerfectRing` (line 317). These connect the separability
  formulation to the node's pth-root formulation over a field. No
  characteristic is excluded.
- `Mathlib.RingTheory.GradedAlgebra.Basic`: `GradedRing`, `GradedAlgebra`
  (line 170) and `GradedAlgebra.proj` (line 229), including docstrings.
  `GradedAlgebra` gives the direct-sum decomposition and graded multiplication.
- `Mathlib.LinearAlgebra.TensorProduct.Graded.Internal`:
  `GradedTensorProduct`, `GradedTensorProduct.of`, its ring/algebra structure,
  and `GradedTensorProduct.tmul_coe_mul_coe_tmul`, including their signatures
  and docstrings. The signed tensor product is reused, not redefined.
- `Mathlib.LinearAlgebra.TensorProduct.Map`: `TensorProduct.map`;
  `Mathlib.LinearAlgebra.TensorProduct.Associator`: `TensorProduct.assoc`,
  `TensorProduct.lid`, `TensorProduct.rid`.
- `Mathlib.LinearAlgebra.Basis.Defs`: `Module.Basis` (line 90), including
  its coordinate-equivalence definition and docstring. A basis here means
  linear independence and spanning, not only one of them.
- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`,
  `Mathlib.Algebra.BigOperators.Group.List.Defs`, and
  `Mathlib.Data.List.OfFn` provide finite dimensionality and the ordered list
  product. The remaining tensor and projection declarations come through
  the public graded-tensor import.

The sole proof-dependency node,
`lem-sfb-graded-bialgebra-coordinate-derivations`, has no recorded Lean
declaration and is still unsplit. It is therefore not imported; the complete
uses of it in steps 2 and 6 remain in the proof docstring. No theorem from
that prerequisite is needed to type this statement. No new definition node,
dependency repair or statement correction is required.

Edge cases checked before writing:

- H = k, with only degree zero: choose r = 0. The basis is the single empty
  product 1, of degree zero. No positive generator or height must be supplied.
- The zero ring is explicitly excluded by the node's `1 ≠ 0` and Lean's
  `[Nontrivial H]`. An empty positive-degree part is allowed.
- Characteristic zero exterior algebras satisfy the statement with height two;
  the sign condition does not require ordinary commutativity.
- In characteristic two, all signs become 1. Truncated polynomial examples
  k[t]/(t^(2^e)) with primitive t and positive degree are admitted, including
  a height greater than two. No division by two or odd-characteristic
  assumption occurs.
- In odd characteristic, truncated polynomial examples in positive even
  degree and exterior generators in odd degree are both allowed. A degree
  greater than one is allowed without any H^1 or top-degree condition.
- Every exponent, including zero and N_j - 1, is present; N_j ≥ 2 ensures
  exponent one is present. Ordered products preserve the signed meaning.
- The universe parameters `u v` are independent; the field and algebra need
  not live in the same universe. All binders and universes are explicit,
  with `autoImplicit false`.

Searches actually run (through the prescribed `msearch.py`, logged in the
sandbox's `searches.jsonl`):

- LeanSearch: `Finite dimensional connected graded commutative bialgebra over
  a perfect field has a homogeneous bounded ordered monomial basis`.
  Eight hits, including homogeneous finite generation, symmetric/polynomial
  monomial bases and `GradedAlgebra`. None states this bounded basis theorem
  for a general finite signed bialgebra.
- LeanFinder: `Borel theorem finite graded signed commutative Hopf algebra
  homogeneous nilpotent generators monomial basis`. Eight hits, comprising
  homogeneous generation and ordinary Hopf-antipode identities; no match.
- Loogle: `Bialgebra, GradedAlgebra`. Zero hits.
- Grep in Mathlib `RingTheory`:
  `Borel|[Gg]raded.*[Bb]ialgebra|[Ss]igned.*[Tt]ensor|monomial.*basis`.
  Four hits, all `MvPolynomial/Basic.lean` monomial bases, which concern a
  polynomial algebra rather than this theorem. A second grep query
  `Borel|[Gg]raded.*[Hh]opf|monomial.*basis` gave the same four hits.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for Borel,
  graded/bialgebra combinations, monomial-basis names and signed tensor
  constructions found the related equality criterion and coherent cohomology
  bialgebra, but no copy of the present theorem. The exact node-id grep in
  `lean/WeilConjectures` found no declaration. The proposed full declaration
  name was also searched in Mathlib, both project roots, and
  `dag/lean_names_upstream.json`, with no collision.

No `STATEMENT-DISPUTED` issue was found. The statement is unchanged.

Validation: the prescribed `scompile.py Q13
lem-sfb-borel-graded-bialgebra-monomial-basis` compiled the delivered module
in both its sandbox and library contexts on the server, with no errors or
warnings (3.1 s and 3.6 s respectively). The only postponed proof is the
named theorem belonging to this DAG node. Delivery preflight is run after
this report and the exact signature record are prepared.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
