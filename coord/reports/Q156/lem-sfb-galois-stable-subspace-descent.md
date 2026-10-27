## Worker report

The module `Sheaf.FieldTheory.GaloisStableSubspaceDescent` states
`Submodule.galois_stable_subspace_descent`, with its whole proof `sorry`. There
are no new definitions, new nodes, dependency repairs, or statement corrections.
Only the item's `lean` record changes. The module docstring identifies the
canonical tensor-factor swap; the theorem docstring carries all five steps of
the accepted proof, including the minimal-support argument and basis extension.

Source read: Milne, Algebraic Groups (2017), Appendix A.64–A.65, printed
pp. 580–581 (PDF physical pages 592–593 in the supplied copy). A.64 actually
uses `K ⊗ V`, as Mathlib does. A.65 applies the result to an invariant ideal.
The node's agent-written finite-support proof was read in full. The current
blueprint's `sk-thm-sf-ctf-stability/_section.md` was also read; this supporting
lemma changes no unit statement or proof route. There is no repair note.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field `k` is `(k : Type u) [Field k]`; `L/k` is `(L : Type v) [Field L]
  [Algebra k L]`. The normal separable algebraic condition is `[IsGalois k L]`:
  `IsGalois` contains `Algebra.IsSeparable` and `Normal`; each already implies
  algebraicity. No `FiniteDimensional` hypothesis is imposed on the extension.
- `Γ = Aut_k(L)` is the binder `σ : L ≃ₐ[k] L`. An arbitrary `k`-vector space
  is `(M : Type w) [AddCommGroup M] [Module k M]`, with independent universes
  for `k`, `L`, and `M` and no dimension restriction.
- The scalar extension is `L ⊗[k] M`, with Mathlib's first-factor `L`-module
  structure. This is the standard dependency interface already recorded on
  def-weil-module-base-change and def-weil-vector-space-scalar-extension.
  Under `TensorProduct.comm k M L`, the node's `m ⊗ λ` becomes `λ ⊗ m`;
  scalar multiplication by `a` becomes `(a * λ) ⊗ m`. It is the same scalar
  extension with the same scalar action, expressed in the library's order.
- The action is `σ.toLinearMap.rTensor M`, whose defining pure-tensor formula
  is `λ ⊗ m ↦ σ(λ) ⊗ m`. `rTensor` extends this additively and `k`-linearly.
  It is not asserted to be `L`-linear. The `L`-subspace is
  `W : Submodule L (L ⊗[k] M)`. Hypothesis `hW` states equality of its image
  and itself under this action, as `k`-subspaces using `restrictScalars k`.
  Restriction does not change the carrier, so this is exactly `σ_M(W) = W`.
- The map `ι(m) = 1 ⊗ m` is `TensorProduct.mk k L M 1`. The subspace
  `W₀ = {m | 1 ⊗ m ∈ W}` is exactly
  `(W.restrictScalars k).comap (TensorProduct.mk k L M 1)`, using Mathlib's
  submodule construction rather than defining a private copy.
- The canonical inclusion of `W₀` into `M` is that comap's `.subtype`.
  `LinearMap.baseChange L` extends it to an `L`-linear map, with the formula
  `λ ⊗ w ↦ λ ⊗ (w : M)`. The conclusion's first conjunct is
  `Function.Injective` of precisely this map. The second conjunct is
  `LinearMap.range` of precisely the same map equal to `W`.
- The node's final isomorphism assertion is explicitly introduced there as
  equivalent to injectivity plus exact image. These two conjuncts state that
  equivalent form: restrict the codomain of this canonical map to its range
  `W` to obtain a bijective `L`-linear map, hence the claimed isomorphism.
  No arbitrary isomorphism or scalar-extension map is substituted.

Dependency declarations read and used:

- def-weil-field: `Field`, `Mathlib.Algebra.Field.Defs`, lines 169–180.
- def-pc-field-extension: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, lines 95–103.
- def-weil-module-base-change: `LinearMap.baseChange`,
  `Mathlib.LinearAlgebra.TensorProduct.Tower`, lines 657–667, including the
  pure-tensor formula. Its node record already documents the factor swap.
- def-weil-pbc-module-tensor-product: `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, lines 77–90; `TensorProduct.mk`,
  lines 374–383; `TensorProduct.lift` and `ext'`,
  `Mathlib.LinearAlgebra.TensorProduct.Basic`, lines 117–140;
  `LinearMap.rTensor`, `Mathlib.LinearAlgebra.TensorProduct.Map`, lines 328–346.
- def-weil-pbc-separable-algebraic-extension: `Algebra.IsSeparable`,
  `Mathlib.FieldTheory.Separable`, lines 540–573. Its algebraicity instance
  and the full `IsGalois` definition in Galois.Basic lines 54–69 were read.
- The supporting `Submodule.restrictScalars`, `comap`, `subtype`, and
  `LinearMap.range` definitions were read in Submodule.RestrictScalars,
  Submodule.Map, Submodule.LinearMap, and Submodule.Range respectively.
- Proof-only imports provide the recorded proof dependencies:
  `Module.Basis.extend` (Mathlib.LinearAlgebra.Basis.VectorSpace, lines 51–62),
  `Module.Basis.baseChange` (Mathlib.LinearAlgebra.TensorProduct.Basis,
  lines 63–80), and `InfiniteGalois.fixedField_fixingSubgroup`
  (Mathlib.FieldTheory.Galois.Infinite, lines 85 onward). They are ordinary,
  non-public imports. The statement dependencies are supplied by the public
  Galois.Basic, TensorProduct.Tower, and Submodule.RestrictScalars imports.

Edge cases checked mathematically against the signature: `M = 0`, `W = 0`,
`W = ⊤`, and `L = k` all have their expected canonical inclusion and image.
For a proper conjugation-unstable line in `ℂ ⊗[ℝ] ℝ²`, `hW` fails as required.
Conjugation-stable lines are generated over `ℂ` by the corresponding real line.
Positive characteristic, infinite algebraic normal separable extensions such
as an algebraic closure of a finite field, and infinite-dimensional `M` are
all permitted. There is no continuity hypothesis to add: each vector of the
canonical scalar extension has finitely many algebraic coefficients, and the
canonical action (and its restriction to `W`) is continuous for the discrete
vector-space topology used in A.64. No separable nonnormal or transcendental
extension is silently admitted.

Searches actually run with `msearch.py`, group Q156 and this item:

- LeanFinder: “A Galois stable subspace of the scalar extension of an arbitrary
  vector space descends to the base field”. Eight results, including
  `Algebra.isInvariant_of_isGalois`, fixed-field results, and intermediate-field
  restriction/extension results. None states invariant-vector-space descent.
- Loogle: `Submodule, TensorProduct, IsGalois`. Zero results.
- LeanSearch: “Galois descent of stable linear subspaces of a tensor product
  vector space”. Eight results, including `Submodule.tensorEquivMul`, linear
  disjointness lemmas, `Submodule.gi`, and `Submodule.tensorSpanEquivSpan`.
  None gives descent of a Galois-stable subspace.
- Mathlib grep via msearch:
  `(galois|Galois|semilinear).*(subspace|submodule|descent)|(subspace|submodule).*galois`.
  Twenty-three displayed hits, primarily Galois connections and semilinear
  submodule maps; no matching theorem. `Submodule.baseChange_eq_span`
  (Tower.lean:839) was separately read: it describes an already descended
  subspace and does not infer descent from Galois stability.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the node id and Galois/subspace/descent
  terms found the parent affine-subgroup theorem's citation and the twisted
  matrix-descent framework, but no declaration of this general statement.
  The matrix-descent invariant definition was opened and is a different,
  twisted finite matrix setting. Exact-name searches for
  `galois_stable_subspace_descent` and `galoisStableSubspaceDescent` in both
  project roots, Mathlib, and the upstream-name registry returned no hits.

Validation: the required `scompile.py` compiled this single module against the
live server library in both sandbox and library checks (8.0 s and 5.7 s), with
no error or unexpected warning. Every universe and variable is explicitly bound.
No statement dispute or source error was found.

## Second reading by Q156

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
