## Worker report

The delivery states `Matrix.commuting_p_power_stable_image` in
`Sheaf.LinearAlgebra.CommutingPPowerStableImage`, with `sorry` as its only theorem
proof. The two accompanying real-data definitions, `Matrix.pPowerSpan` and
`Matrix.scalarExtensionMap`, spell out the sequence and scalar-extension map
introduced by this very node. They are included in `lean.declarations`; neither
introduces an independent mathematical notion needing a new DAG node.

I read the full node, all four statement-dependency records and their recorded
Mathlib declarations/docstrings. I read Milne, Algebraic Groups (2017), printed
pp.376--378, especially the proof of Proposition 17.80, and p.223 before 11.36.
Milne asserts that the semisimple elements form a p-Lie subalgebra in that proof;
the stable-span statement and the imperfect-field argument are explicitly
agent-supplied material in this node, not a verbatim theorem from Milne.
I also checked the latest blueprint unit `sk-thm-sf-ctf-stability/_section.md`;
this node is an auxiliary linear-algebra statement, not the unit statement.
There is no repair-note file for the item. No statement correction is needed.

Hypothesis and clause correspondence:

- The field k is `(k : Type u) [Field k]`. The chosen algebraic closure is
  `(L : Type v) [Field L] [Algebra k L] [IsAlgClosure k L]`. This uses the
  dependency's stated general algebraic-closure predicate, rather than fixing
  one particular implementation. There is no perfectness hypothesis on k.
- Positive characteristic is `(p : ℕ) [CharP k p] (hp : 0 < p)`. No extra
  primality hypothesis is added: a field's positive characteristic is prime.
- The size n >= 1 is `(n : ℕ) (hn : 1 ≤ n)`. The subspace is
  `W : Submodule k (Matrix (Fin n) (Fin n) k)`. Matrix multiplication is
  Mathlib's finite-index matrix product, not entrywise multiplication.
- The commuting hypothesis is `hcomm : ∀ X ∈ W, ∀ Y ∈ W, X * Y = Y * X`.
  Closure under pth powers is `hpow : ∀ X ∈ W, X ^ p ∈ W`.
- The definition of W_r is `pPowerSpan W p r`, exactly
  `Submodule.span k ((fun X ↦ X ^ (p ^ r)) '' (W : Set _))`.
  Here r ranges over ℕ, including zero, and span means finite linear combinations.
- An arbitrary extension is quantified as
  `∀ (K : Type (max u w)) [Field K] [Algebra k K]`. The field homomorphism
  implicit in `Algebra k K` is injective. The free universe w admits arbitrarily
  large extensions; the maximum convention prevents undersized test universes.
  Smaller presentations can be lifted without restricting the mathematics.
- `scalarExtensionMap K W` has domain the actual `K ⊗[k] W`. Its definition
  first applies `LinearMap.baseChange K W.subtype`, then
  `TensorProduct.piRight k K K (fun _ : Fin n ↦ Fin n → k)`, and rowwise
  `TensorProduct.piScalarRight k K K (Fin n)`. On a pure tensor a ⊗ X, the
  (i,j) entry is `(X i j) • a = algebraMap k K (X i j) * a =
  a * algebraMap k K (X i j)`. Thus this is precisely the prescribed canonical
  map, with no arbitrary comparison map or existence-based data choice.
- The first conjunct explicitly gives injectivity of that tensor-to-matrix map.
  For every r it equates
  `LinearMap.range (scalarExtensionMap K (pPowerSpan W p r))` to the K-span
  of p^rth powers of members of
  `LinearMap.range (scalarExtensionMap K W)`. These are the two sides of
  the node's scalar-extension identity, with tensors identified with their images.
- `Antitone (pPowerSpan W p)` states that the sequence is descending, for all
  pairs of indices in their order. The existential `W_infty` is a k-subspace,
  with `W_infty ≤ W`, and `∃ R, ∀ r, R ≤ r → pPowerSpan W p r = W_infty`
  states stabilization at that very subspace.
- `∀ X ∈ W_infty, X ^ p ∈ W_infty` is its p-power closure.
- For every matrix X over k, the first membership equivalence says
  `X ∈ W_infty ↔ X ∈ W ∧ ...`, where the remaining condition is conjugacy
  of `X.map (algebraMap k L)` to `Matrix.diagonal d` by a matrix unit P.
  Units of the matrix ring are exactly the invertible matrices; `↑P⁻¹` is
  its matrix inverse. This is exactly geometric diagonalizability, with no
  assumption of diagonalizability over k itself.
- For every matrix Y over L, the second membership equivalence says that Y is
  in the range of the tensor map for W_infty exactly when it is in the range
  for W and is conjugate over L to a diagonal matrix. This is the entire
  algebraic-closure scalar-extension clause.

Dependency declarations and imports:

- `def-weil-field`: `Field`, defined in `Mathlib.Algebra.Field.Defs`, available
  through the public field-theory import. I read its `CommRing` and
  `DivisionRing` signature and docstring.
- `def-weil-algebraic-closure`: `AlgebraicClosure` in
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`, and the recorded predicate
  `IsAlgClosure` in `Mathlib.FieldTheory.IsAlgClosed.Basic`. The latter's full
  signature and fields supply precisely algebraic extension plus algebraic closure.
- `def-weil-matrix`: `Matrix`, imported from
  `Mathlib.LinearAlgebra.Matrix.Defs`. `Mathlib.Data.Matrix.Basic` provides
  the matrix ring operations and the entrywise map used in the statement.
- `def-weil-module-base-change`: `LinearMap.baseChange`, `TensorProduct`,
  `TensorProduct.mk`, and `TensorProduct.AlgebraTensorModule.distribBaseChange`,
  in the recorded `Mathlib.LinearAlgebra.TensorProduct.Tower` and its imports.
  The actual construction uses `LinearMap.baseChange` directly. Finite-product
  equivalences come from `Mathlib.LinearAlgebra.TensorProduct.Pi`; this is
  composition of existing canonical constructions, not a replacement tensor product.
- Proof-only: `Module.finrank` from `Mathlib.LinearAlgebra.Dimension.Finrank`,
  and `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`
  from `Mathlib.LinearAlgebra.Eigenspace.Pi`, both imported without `public`.
  I read the latter's signature and docstring: finite dimension, pairwise
  commutation and spanning maximal generalized eigenspaces imply spanning
  intersections. `lem-sfb-additive-jordan-linear-compatibility` has no recorded
  Lean declaration or Mathlib match at this reading and hence no import to add.
  It is a proof dependency, not a missing object needed to type this statement.

Edge cases checked before writing:

- W = 0: all the power spans and scalar extensions are zero, W_infty = 0,
  and the zero matrix is diagonalizable. No nonzero-element assumption occurs.
- r = 0: p^0 = 1, so the span is W and the scalar-extension identity is
  the identity. No power of exponent zero is accidentally used for r = 0.
- n = 1: all matrices are diagonal, and a subspace of the one-dimensional
  matrix space is zero or the whole space; in the latter case powers of 1
  show the stable span remains the whole space, even when k is imperfect.
- A square-zero nilpotent line in size 2 has stable span zero, as required.
- Imperfect k = F_2(t), W = kI + kM with M = [[0,t],[1,0]]: M^2 = tI,
  W_1 = kI and all later spans are kI. A matrix aI+bM is geometrically
  diagonalizable exactly when b=0. Over the algebraic closure M has a
  repeated eigenvalue and a nontrivial nilpotent part; this does not wrongly
  label M diagonalizable. The formulation uses spans, never surjectivity of
  the Frobenius map on k.
- Extension K = k is included. No separability, algebraicity, perfectness or
  algebraic-closure hypothesis is imposed on the arbitrary extension K.
  The possibly different universe of the fixed closure L is retained.

Searches for an existing statement or construction (all msearch calls used
Q129 and this item, and their exact structured outputs are in searches.jsonl):

- LeanFinder: "For commuting matrices closed under pth powers the spans of
  iterated pth powers stabilize at the geometrically diagonalizable subspace
  and commute with extension of scalars". Eight hits, including generalized
  eigenspace preservation and the recorded joint-generalized-eigenspaces
  theorem; none states this stable-span theorem.
- Loogle: "Matrix.map, Submodule.baseChange, Module.End.IsSemisimple".
  Zero hits for the combined query. Direct source reads located the relevant
  canonical maps; no exact existing statement was found.
- Mathlib grep via msearch: "stable.*[pP]ower|[pP]ower.*[sS]table|diagonaliz"
  in LinearAlgebra. Three hits, all about semisimplicity and triangularizability;
  no stable power span or scalar-extension assertion.
- LeanSearch: "commuting matrix subspace stable span iterated pth powers
  geometrically semisimple". Eight hits: commuting powers, semisimple powers,
  sums and products, and Submodule.pow_eq_span_pow_set. The last concerns
  products of submodules, not the span of individual Frobenius powers.
- Direct rg searches of `lean/WeilConjectures` and `lean/Sheaf` for
  diagonalizability, stable-power spans and matrix scalar extension found
  geometric semisimplicity of group-scheme points (which uses the same
  conjugation convention) but no duplicate theorem or scalar-extension map
  for a matrix subspace. The exact item-id search of WeilConjectures returned
  nothing. Proposed names were also checked against dag/lean_names_upstream.json,
  the project's LinearAlgebra directories, and Mathlib's LinearAlgebra sources.
- Direct Mathlib API searches located `LinearMap.baseChange`,
  `TensorProduct.piRight`, `TensorProduct.piScalarRight`, and `Submodule.baseChange`.
  The latter lands in a tensor space, so composing the canonical tensor
  equivalences is still needed to obtain the node's actual matrix-space map.

Validation: `scompile.py` compiled the delivered file both as the sandbox module
and under its final library module name, cleanly (1.4 s and 1.5 s). All variables
and universes are explicitly bound; `autoImplicit` is false. Every Lean line
has at most 100 characters. The node copy changes only `lean`. The theorem's
full seven-step natural-language proof plan is in its docstring, including
both directions of the scalar-extension and diagonalizability arguments.

## Second reading by Q129

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
