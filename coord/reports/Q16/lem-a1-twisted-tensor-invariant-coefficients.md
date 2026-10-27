## Worker report

The module `Sheaf.RingTheory.TwistedTensorInvariantCoefficients` states
`RingHom.twistedTensor_invariant_coefficients`, with its proof entirely `sorry`.
Its four helpers specialize existing Mathlib constructions to the two algebra
structures on the same ring. They introduce no independent mathematical notion,
and their data are fully defined: no choice of an unspecified tensor product,
ring structure or inclusion map, and no postponed theorem used to define data.
All five declarations have source/blueprint docstrings and are listed in
`lean.declarations`.

Source read: `literature/stacks-project/groupoids.tex`, Tag 03C8,
`groupoids-lemma-basis`, especially the second diagram and its explanation
(lines 4791–4812). In that diagram the left vertical arrow takes the formal basis
vector to `c(t(x_i)) = p₀(t(x_i))`; the horizontal maps compare coefficients
through `s` and `t`. The already reviewed node extracts exactly these two clauses.
No statement correction, new node or dependency repair was needed.

Hypotheses and objects, matched to the node:

- Commutative rings A and B: `{A : Type u} {B : Type v} [CommRing A] [CommRing B]`,
  with independent, explicit universes and no nonzero-ring restriction.
- Unital maps σ and τ: `(σ τ : A →+* B)`.
- D = B tensor_(σ,A,τ) B: `RingHom.TwistedTensorProduct σ τ` is definitionally
  `@TensorProduct A _ B B _ _ σ.toAlgebra.toModule τ.toAlgebra.toModule`.
  The first action is σ and the second action is τ; neither is registered as a
  file-local instance, so they cannot be accidentally conflated.
- The tensor ring structure is exactly Mathlib's
  `Algebra.TensorProduct.instCommRing`, instantiated with those two algebras.
  `instCommRingTwistedTensorProduct` only exposes that existing instance for this
  explicit specialization; it does not construct another multiplication.
- p₀(b) = b tensor 1: `twistedTensorLeft σ τ` is exactly Mathlib's
  `Algebra.TensorProduct.includeLeftRingHom` for the same algebras.
- p₁(b) = 1 tensor b: `twistedTensorRight σ τ` is exactly the underlying ring
  homomorphism of Mathlib's `Algebra.TensorProduct.includeRight`, again with the
  two algebras passed explicitly. Its `AlgHom.toRingHom` projection also receives
  the algebras explicitly; inference otherwise seeks one algebra on both factors.
- The ring map Δ: `(Δ : B →+* TwistedTensorProduct σ τ)`.
- Δσ = p₁σ: `_hΔσ : Δ.comp σ = (twistedTensorRight σ τ).comp σ`.
- Δτ = p₀τ: `_hΔτ : Δ.comp τ = (twistedTensorLeft σ τ).comp τ`.
- The finite nonempty index and the elements of A: `(r : ℕ) (_hr : 1 ≤ r)`
  and `(x : Fin r → A)`. The zero-based `Fin r` reindexes the node's 1,…,r.
- The basis hypothesis is the node's explicit meaning, word for word:
  `_hbasis : ∀ b : B, ∃! c : Fin r → A,
  b = ∑ j : Fin r, σ (c j) * τ (x j)`.
  Since the index is finite, this is the same finite-coordinate characterization
  of the recorded `Module.Basis` notion, with scalar action through σ.

Conclusions, matched to the node:

- The first conjunct supplies `∃ e : @Module.Basis (Fin r) B
  (TwistedTensorProduct σ τ) _ _ (twistedTensorRight σ τ).toAlgebra.toModule`.
  This is precisely a B-basis for multiplication through p₁, not the usual
  default left-factor action on an algebra tensor product. The following
  `∀ j : Fin r, e j = twistedTensorLeft σ τ (τ (x j))` specifies exactly the
  vectors p₀(τ(x_j)), including their order.
- The second conjunct quantifies over every `a : A` and every coefficient vector
  `c : Fin r → A` satisfying `τ a = ∑ j, σ (c j) * τ (x j)`, and concludes
  `∀ j : Fin r, σ (c j) = τ (c j)`. By `_hbasis` there is exactly one such
  vector for each a. Quantifying over a vector with its expansion equation is
  therefore exactly the assertion about the unique coefficients, without making
  a second choice or adding a hypothesis. The equality is in B; no cancellation
  or injectivity hypothesis on p₁ is hidden.

Dependency declarations read and used:

- `def-weil-pbc-module-tensor-product` is a Mathlib leaf. Its recorded
  `TensorProduct`, `TensorProduct.mk`, `TensorProduct.lift`, `lift.tmul`,
  `TensorProduct.ext'` and `LinearMap.rTensor`/`rTensorHom` interfaces were read
  in `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic` and `.Map`.
  The statement uses that exact `TensorProduct`, through the owning helper.
- `def-weil-pbc-free-module` records `Module.Free` in
  `Mathlib.LinearAlgebra.FreeModule.Basic`. Its signature and the definition of
  `Module.Basis` in `Mathlib.LinearAlgebra.Basis.Defs` were read. A basis is a
  linear equivalence to finitely supported coordinates; the first conclusion
  uses this exact `Module.Basis`, and the input uses the node's finite unique
  expansion formulation. Public import: `Mathlib.LinearAlgebra.FreeModule.Basic`.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property` is a Mathlib leaf.
  Its recorded ring structure, `tmul_mul_tmul`, `includeLeft`, `includeRight`
  and `ext` in `Mathlib.RingTheory.TensorProduct.Basic` were read, as were
  `productMap`, `productMap_apply_tmul`, `productMap_left` and `productMap_right`
  in `.Maps`. The helpers use `instCommRing`, `instAlgebra`,
  `includeLeftRingHom` and `includeRight` from that canonical construction.
  `.Basic` is public; `.Maps` is imported for the recorded proof dependency.
- The proof-only Mathlib leaf `lem-weil-pbc-free-module-base-change-free` records
  `Module.Basis.baseChange` and `Module.Basis.baseChange_apply` in
  `Mathlib.LinearAlgebra.TensorProduct.Basis`. Their full signatures and
  docstrings were read. This module is imported as a proof dependency.

Edge cases checked before writing: r = 1; σ = τ (including both identity maps);
arbitrary different σ and τ subject only to the stated Δ identities; both rings
zero; and B zero with A nonzero. The last case cannot satisfy the unique-expansion
hypothesis for r ≥ 1, as two distinct coefficient vectors give the same element.
The all-zero case is permitted, as it must be. r = 0 is excluded exactly by the
node. Nilpotents and arbitrary characteristics remain allowed. Neither ring map
is assumed injective or surjective, Δ has no extra counit or coassociativity law,
and there is no extra faithful-flatness or domain hypothesis. Both rings can
live in unrelated universes; the tensor is in B's universe, as in Mathlib.

Searches made before writing (all returned no exact combined statement):

- `msearch.py ... leanfinder`: “Invariant coefficients of tau(a) expanded in a
  sigma linear basis tau(x_i), using Delta sigma equals p1 sigma and Delta tau
  equals p0 tau”. Eight hits on differentials, cotangent generators, polynomial
  characteristic matrices and presentations; none gives this comparison.
- `msearch.py ... loogle`: `Module.Basis.baseChange`. Three hits:
  `Module.Basis.baseChange`, `.baseChange_apply`, `.baseChange_repr_tmul`.
  These provide the already recorded first proof step, not the Δ coefficient
  comparison of this node.
- `msearch.py ... grep`:
  `eqLocus.*[Bb]asis|[Bb]asis.*eqLocus|[Ii]nvariant.*[Cc]oefficient|[Cc]oefficient.*[Ii]nvariant`.
  Three irrelevant Lie-loop and meromorphic-coefficient hits.
- `rg -n` in the project's `lean/WeilConjectures` and `lean/Sheaf`, first for
  twisted/invariant-coefficient/affine-groupoid terminology, then narrowed to
  `twistedTensor|twisted_tensor|invariantCoefficients|invariant_coefficients`;
  the latter also searched `dag/lean_names_upstream.json`. No declaration with
  these names or this combined statement was found. The affine groupoid basis
  descent theorem is a consumer with additional groupoid hypotheses and different
  conclusions, not this statement.
- Searched the exact node id in `lean/WeilConjectures`: no match.

Validation: the delivered module compiles cleanly through the prescribed
`scompile.py`, separately in sandbox and library mode. The first version exposed
an implicit-algebra inference issue in projecting `includeRight.toRingHom`;
passing the two relevant algebra structures explicitly fixed it. The final
module has no diagnostic commands, no lines over 100 characters, no auto-bound
variables, no local notation or local instances, and only the main theorem has
`sorry`. No statement is disputed.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
