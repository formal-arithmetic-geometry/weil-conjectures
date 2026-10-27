## Worker report

The module `Sheaf.RingTheory.BoundedBialgebraExterior` states
`GradedAlgebra.bounded_bialgebra_exterior`, with its sole proof `sorry`.
It constructs no new objects or definitions and changes only the item's `lean` record.
The source is Milne, Abelian Varieties I Lemma 12.2, printed p.55, equality case.
I read this lemma, its proof, and formula (3) immediately above it in the local PDF.
The accepted stage-1 node spells out the bialgebra hypotheses; those are retained exactly.
No statement correction or disputed statement is needed.

Hypotheses, clause by clause:

- The field is `(k : Type u) [Field k] [PerfectField k]`. `Field` is the recorded
  Mathlib match for `def-weil-field`. Mathlib's `PerfectField` uses separability;
  `PerfectField.toPerfectRing` supplies the equivalent bijective Frobenius condition
  in positive characteristic. Thus it includes characteristic zero and every perfect
  positive-characteristic field, as the node specifies.
- A graded unital associative algebra is `(H : Type v) [Ring H] [Algebra k H]`,
  with `(𝒜 : ℕ → Submodule k H) [GradedAlgebra 𝒜]`. This is Mathlib's internal
  direct-sum grading: `DirectSum.decomposeAlgEquiv 𝒜` identifies H with the direct sum
  of its homogeneous pieces, respecting multiplication and scalars. The field universe
  `u` and algebra universe `v` are independent and explicitly bound.
- Finite dimensionality is `[FiniteDimensional k H]`.
- The equation H^0 = k times 1 is `hconnected : 𝒜 0 = Submodule.span k {(1 : H)}`.
  The nonzero unit is `[Nontrivial H]`; no commutativity of the underlying ring is imposed.
- The sign rule is `hcomm`, quantifying all degrees `i j` and homogeneous elements
  `x : 𝒜 i`, `y : 𝒜 j`, with scalar `(-1 : k) ^ (i * j)`.
- The coproduct is `(Δ : H →ₗ[k] H ⊗[k] H)`. `hdegree` says that Δ of a degree-n
  element is in the span of pure tensors whose two degrees add to n. This is precisely
  total-degree preservation; a span permits every finite sum, not just a pure tensor.
- The specified signed multiplication is Mathlib's `GradedTensorProduct k 𝒜 𝒜`,
  transported from the ordinary underlying tensor vector space by
  `GradedTensorProduct.of k 𝒜 𝒜`. Its theorem `tmul_coe_mul_coe_tmul` gives exactly
  `(a tensor b)(c tensor d) = (-1)^(deg b * deg c) ac tensor bd`.
  `hmul` requires Δ to preserve this multiplication. `hunit` requires Δ(1) = 1 tensor 1.
  Together with Δ's linearity these are exactly a unital k-algebra map, including scalar
  preservation, without an additional arbitrary multiplication or map.
- Coassociativity is `hcoassoc`, using the canonical `TensorProduct.assoc` and
  `TensorProduct.map`. Both sides lie in `H ⊗[k] (H ⊗[k] H)`.
- The counit `(ε : H →ₗ[k] k)` is the degree-zero projection: `hprojection` says
  that embedding ε(x) as a scalar of H equals `GradedAlgebra.proj 𝒜 0 x`.
  Since H is nontrivial and k is a field, this characterizes ε uniquely. It is
  equivalent to using the inverse of the scalar identification H^0 = k.
- Both counit identities are in `hcounit`, using `TensorProduct.lid` and
  `TensorProduct.rid`. Neither identity is omitted or assumed only on generators.
- `(g : ℕ)` permits g = 0. `hdim : Module.finrank k (𝒜 1) = g` is the stated
  dimension equality, and `hbound` says every homogeneous submodule above g equals zero.

Conclusions, clause by clause:

- The first conjunct is `∀ x : 𝒜 1, (x : H) * (x : H) = 0`, including characteristic two.
- The existential `e : ExteriorAlgebra k (𝒜 1) ≃ₐ[k] H` is an isomorphism of the
  entire unital k-algebras, not just a linear isomorphism or degreewise dimensions.
- Its product formula is the first conjunct under this existential: for every n and
  tuple `x : Fin n → 𝒜 1`, `e (ExteriorAlgebra.ιMulti k n x)` equals the ordered
  product `(List.ofFn fun i ↦ (x i : H)).prod`. At n = 1 this fixes each generator,
  so the equivalence is the canonical map induced by multiplication, not an arbitrary
  algebra equivalence. At n = 0 this gives the empty product 1.
- The last conjunct says that the image of `ExteriorAlgebra.exteriorPower k n (𝒜 1)`
  under `e.toLinearMap` equals `𝒜 n` for every n. Thus e and its inverse preserve
  the grading; this is exactly a graded algebra isomorphism expressed with Mathlib's
  actual exterior powers as submodules. No homogeneous degree is omitted.

Dependency declarations read and used:

- `def-weil-field`: `Mathlib.Algebra.Field.Defs`, `Field` (a Mathlib leaf;
  no Lean record is required).
- `def-weil-pbc-exterior-algebra`: `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic`,
  `ExteriorAlgebra`, `ExteriorAlgebra.ι`, `ExteriorAlgebra.exteriorPower` and
  `ExteriorAlgebra.ιMulti`; also `Mathlib.LinearAlgebra.ExteriorAlgebra.Grading`,
  `ExteriorAlgebra.gradedAlgebra`. The node's short `exteriorPower` is qualified
  here so the theorem's signature reads outside the ExteriorAlgebra namespace.
- Stated proof dependencies are imported privately:
  `lem-trf-exterior-power-universal-property` uses
  `Mathlib.LinearAlgebra.ExteriorPower.Basic`, `exteriorPower.alternatingMapLinearEquiv`;
  `lem-weil-pbc-exterior-power-free-basis` uses that module and
  `Mathlib.LinearAlgebra.ExteriorPower.Basis`, `Module.Basis.exteriorPower`,
  `exteriorPower.coe_basis`, `exteriorPower.finrank_eq`,
  `exteriorPower.zeroEquiv`, and `exteriorPower.oneEquiv`.
- `lem-sfb-borel-graded-bialgebra-monomial-basis` is an existing proof prerequisite
  with no recorded Lean declaration or Mathlib match. It is not needed to type this
  theorem and is not imported. Its source-based application and all remaining proof
  steps are preserved in the theorem's docstring for stage 3. It is not a new notion
  or a missing statement dependency of the current statement.

Edge cases checked before writing:

- g = 0 gives H = H^0 = k and H^1 = 0, so the exterior algebra is k. The empty
  tuple, zero-dimensional degree-one space, and all degrees n > 0 remain included.
- In characteristic two, `-1 = 1`, so neither signed commutativity nor Δ's signed
  multiplicativity alone forces a square to vanish. The claimed square-zero property
  remains a conclusion of the bounded criterion, never an added hypothesis.
- A height-four primitive truncated polynomial algebra in characteristic two has
  one-dimensional H^1 but a nonzero degree-three part; the bound with g = 1 excludes it.
- Exterior algebras on one or two generators with primitive coproduct meet the
  hypotheses, including the signed tensor multiplication on mixed terms.
- No symmetry/cocommutativity of Δ, characteristic restriction, choice of homogeneous
  basis, or finite index type is added. The zero algebra is excluded precisely by the
  node's nonzero-unit clause.

Searches for an existing statement:

- `msearch.py leanfinder`: "A finite dimensional connected graded commutative bialgebra
  over a perfect field vanishing above dimension H1 is exterior algebra on H1".
  Eight hits: ExteriorAlgebra, its grading, square-zero generator and lift APIs, plus
  unrelated H1-cotangent results. No bounded bialgebra theorem.
- `msearch.py loogle`: `"Bialgebra", "ExteriorAlgebra"`. Zero hits.
- `msearch.py grep`: `graded.*[Bb]ialgebra|[Bb]ialgebra.*graded|[Bb]ounded.*[Ee]xterior`.
  Zero hits.
- `msearch.py leansearch`: "A connected finite dimensional graded Hopf algebra
  vanishing above dimension of degree one is the exterior algebra". Eight hits:
  ExteriorAlgebra, grading, hom_ext, presentation and lift APIs, no criterion.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `bounded_bialgebra_exterior|bounded.*bialgebra|bialgebra.*exterior|exterior.*bialgebra`
  found no exact statement or name collision. The upstream declaration index also
  contains no item-id hit.
- Broader `rg` for bialgebra, Hopf algebra and graded tensor product found
  `Sheaf.AlgebraicGeometry.CoherentGroupBialgebra`; I read it in full. It constructs
  the particular cohomology bialgebra, rather than proving the abstract exterior
  criterion. Ordinary Hopf-algebra files use unsigned tensor multiplication and
  are not substitutes. Mathlib's graded tensor product Internal/External files
  supply exactly the signed multiplication needed here.

Validation: compiled through `scompile.py` against the live published library.
The first compile detected an unqualified exterior-power name; it was changed to
`ExteriorAlgebra.exteriorPower`. The final signature binds every variable and universe
explicitly. The delivery dry run also compiles the file and checks the node record.

The inherited BLOCKED ending concerned stage-1 `deliver.py`'s prohibition on reopening
an accepted split. The live queue assigns this item to stage 2 and its Lean record is
absent. The stage handoff in brief-stage2 section 0 explicitly authorizes stating it;
the accepted split, proof, dependencies, and stage-1 review are unchanged.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
