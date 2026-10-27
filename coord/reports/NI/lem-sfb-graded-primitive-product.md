## Worker report

The module `Sheaf.RingTheory.GradedPrimitiveProduct` states
`GradedAlgebra.primitive_product_ne_zero`, with the sole proof `by sorry`.
It records the primitive-product assertion of the assigned node unchanged.
There are no additional definitions, dependency repairs, statement corrections,
or mathematical disputes.

Hypothesis and conclusion correspondence:

- The field is `(k : Type u) [Field k]`. The algebra is
  `(H : Type v) [Ring H] [Algebra k H] [Nontrivial H]`; `Ring` gives associative
  unital multiplication without commutativity, and `Nontrivial` is precisely
  the stipulated inequality `1 ≠ 0`. The coefficient and algebra universes are
  independent and explicitly declared.
- The nonnegative direct-sum grading is `(𝒜 : ℕ → Submodule k H)
  [GradedAlgebra 𝒜]`. Mathlib defines this as `GradedRing 𝒜`, including the
  internal direct-sum decomposition and homogeneous unit/multiplication.
  Thus it does not merely assume a filtration or a spanning family.
- `H^0 = k·1` is `hconnected : 𝒜 0 = Submodule.span k {(1 : H)}`.
- The coproduct is `Δ : H →ₗ[k] H ⊗[k] H`. Its degree preservation is
  `hdegree`: for a homogeneous input of degree `n`, its output belongs to the
  span of pure tensors of degrees `p,q` with `p + q = n`. This is exactly the
  total-degree piece of the tensor product, including arbitrary finite sums.
- `hunit` states `Δ 1 = 1 ⊗ₜ 1`. `hmul` states multiplicativity after the
  canonical linear equivalence `GradedTensorProduct.of k 𝒜 𝒜` to Mathlib's
  signed tensor algebra. Its theorem `tmul_coe_mul_coe_tmul` gives exactly
  the sign `(-1)^(deg b * deg c)`. Combined with linearity and preservation
  of the unit, these clauses say that Δ is a unital k-algebra homomorphism
  for that multiplication. Scalar compatibility follows by applying linearity
  to `a • 1`; it is not an extra hypothesis.
- `hcoassoc` is `(Δ ⊗ id)Δ = (id ⊗ Δ)Δ` after the ordinary canonical
  associator `TensorProduct.assoc k H H H`. Coassociativity does not insert
  a swap or a Koszul sign. All tensor maps use the recorded module tensor
  product, rather than an arbitrary comparison map.
- Every integer `r ≥ 0` is represented by `(r : ℕ)`, and degree-one vectors
  by `x : Fin r → 𝒜 1`. `hindependent` is `LinearIndependent k` of their
  inclusions into H, equivalent to independence in the degree-one subspace.
  `hprimitive` is the displayed equality
  `Δ (x i) = x i ⊗ₜ 1 + 1 ⊗ₜ x i` for each index.
- The conclusion says that `(List.ofFn fun i : Fin r ↦ (x i : H)).prod`
  belongs to `𝒜 r` and is nonzero. `List.ofFn` enumerates Fin r in increasing
  order and `List.prod` preserves that order in a general monoid. Its empty
  product is 1, so the node's empty-product clause is built into the expression.
- There is no assumption on characteristic or individual squares, and no
  assumption of finite dimension, graded commutativity, a counit or antipode.

Dependency declarations read and used:

- `def-weil-field`: Mathlib's `Field`, read in
  `Mathlib/Algebra/Field/Defs.lean`, including its `CommRing` and `DivisionRing`
  parents. This is a Mathlib leaf and does not need a separate Lean record.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` and `TensorProduct.tmul`
  in `Mathlib.LinearAlgebra.TensorProduct.Defs`; `TensorProduct.lift` and
  `TensorProduct.ext'` in `Mathlib.LinearAlgebra.TensorProduct.Basic` give the
  contraction/universal property used by the proof. The module imports the
  graded tensor product and associator modules, which publicly supply this API.
- Proof-only dependency `lem-sfb-linear-map-extension-prescribed-value` is
  Mathlib's `LinearMap.exists_extend_of_notMem`, whose full statement and proof
  were read in `Mathlib.LinearAlgebra.Basis.VectorSpace`, lines 294–301. Its
  module is imported without `public` for stage 3. The theorem needs no finite
  dimension and permits the prescribed value 1. No leaf is redefined.

Other Mathlib interfaces read: `GradedAlgebra`/`GradedRing`,
`GradedTensorProduct.of`, its signed multiplication formula and `instAlgebra`,
`TensorProduct.map`, and `TensorProduct.assoc`. Related project modules
`GradedBialgebraCoordinateDerivations`, `BoundedBialgebraExterior`, and
`BorelBialgebraMonomialBasis` use the same linear-coproduct interface; their
stronger and different theorems are not imported as prerequisites.

Source and proof check: read Milne AV, printed p.55 (PDF page 61), Lemma 12.2
and identity (3). Milne invokes Borel's structure theorem; the assigned node
explicitly supplies an elementary replacement only for the primitive-product
ingredient. The declaration's docstring includes all four accepted proof steps:
prefix induction; separating functional on degree one from the prescribed-value
extension leaf; the ordered signed subset expansion; and the tensor contraction
which leaves only the last singleton. The source and proof dependency graph
are preserved, and no exterior-algebra conclusion is claimed.

Edge cases checked mathematically before writing:

- `r = 0`: the vector-family hypotheses are vacuous, the product is 1,
  `GradedAlgebra` places it in degree zero, and `Nontrivial H` makes it nonzero.
- `r = 1`: independence forces the single vector nonzero; the product is that
  vector and already has degree one.
- Characteristic two: Mathlib's integer-unit sign acts as +1 after scalar
  reduction; the separating functional proof does not divide by 2 or by r!.
- Nonzero squares are allowed, e.g. the one-generator tensor algebra with its
  primitive generator. The assertion for one independent vector remains valid.
- Noncommutative H: increasing order is fixed by the list, with no permutation
  of factors. The sign formula only moves across the two tensor axes.
- Infinite-dimensional H and H^1 are allowed; no finite-dimensional instance
  is requested. The functional extension is valid for arbitrary vector spaces.
- The zero algebra is excluded exactly by the node's `1 ≠ 0` hypothesis; H = k
  with zero positive degrees satisfies only the empty independent-family case.

Searches for an existing statement (logged by msearch in `searches.jsonl`):

- `leanfinder`: “Linearly independent degree one primitive elements in a signed
  graded bialgebra have nonzero ordered product”. Eight hits concern group-like
  independence or direct-sum product support vanishing; none states this result.
- `leansearch`: “The ordered product of linearly independent degree one primitive
  vectors in a connected graded algebra with signed coproduct is nonzero”.
  Eight hits include `GradedTensorProduct.tmul_coe_mul_coe_tmul`, graded product
  support, and graded commutation. The signed multiplication notion exists in
  Mathlib and is reused; no primitive-product nonvanishing theorem was found.
- `loogle`: `GradedAlgebra, TensorProduct` locates the Mathlib graded tensor
  product API. `GradedTensorProduct.tmul_coe_mul_coe_tmul` locates precisely
  its existing homogeneous multiplication formula.
- `msearch grep`: `(primitive|comul).*(linearIndependent|prod_ne_zero)|
  (linearIndependent|prod_ne_zero).*(primitive|comul)` in Mathlib: zero hits.
- `rg` in the live read clone's `lean/WeilConjectures` and `lean/Sheaf` for
  the item ID and `primitive_product_ne_zero|graded_primitive_product|
  primitiveProduct`: no existing declaration of this assertion. Broader searches
  for `GradedTensorProduct` and signed tensor products located the three related
  bialgebra modules discussed above and the consumer `StructureSheafH1Dimension`;
  these do not already state this node. Mathlib's Internal/External graded
  tensor-product modules were read in full where relevant.

Validation: `scompile.py NI lem-sfb-graded-primitive-product` compiled the single
module against the published live server library, both sandbox and library passes,
with no errors or warnings. `autoImplicit false` ensures every variable is bound.
The node copy changes only `lean`, with its signature extracted verbatim from
the file, explicit universes, UTC date, and NI attribution. All lines are at most
100 characters. No direct repository edits or Git commands were run.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
