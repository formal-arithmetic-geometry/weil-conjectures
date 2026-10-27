## Worker report

The module `Sheaf.LinearAlgebra.RationalPositiveDefiniteFeasibility` states
`Matrix.exists_rat_posDef_of_real_solution`, with `sorry` as its entire proof.
It also constructs `Matrix.rationalSymmetricRealExtension`, the actual real linear
map specified by the node, using Mathlib linear-map sums, projections and `LinearMap.pi`.
The construction has no postponed proof or chosen data. The node changes only in `lean`.
No statement correction, dependency repair or new node is necessary.

Hypothesis-by-hypothesis and clause-by-clause comparison:

- The rational and real fields are Mathlib `ℚ` and `ℝ`, with the usual rational cast.
  The dependency `def-weil-field` records Mathlib `Field`; its declaration in
  `Mathlib.Algebra.Field.Defs` extends `CommRing` and `DivisionRing`, the latter
  supplying nontriviality and inverses of nonzero elements. No field notion is copied.
- Nonnegative dimensions, including zero, are `{n m : ℕ}`. Matrix indices are
  `Fin n`; target coordinates are `Fin m`.
- `Sym_n(F)` is the existing Mathlib type `selfAdjoint (Matrix (Fin n) (Fin n) F)`.
  `selfAdjoint` is the additive subgroup cut out by `star A = A`, with the usual
  scalar module structure for scalars with trivial star. For matrices, star is
  conjugate transpose. `Matrix.isHermitian_iff_isSelfAdjoint` and
  `Matrix.isHermitian_iff_isSymm` identify this with exactly symmetry over both
  `ℚ` and `ℝ`. There is no extra hypothesis on the matrices.
- The arbitrary rational linear map is
  `L : selfAdjoint (Matrix (Fin n) (Fin n) ℚ) →ₗ[ℚ] (Fin m → ℚ)`;
  the arbitrary rational right hand side is `b : Fin m → ℚ`.
- The specified real linear extension is the helper `rationalSymmetricRealExtension L`.
  Its `k`-th coordinate is the sum over `i ≤ j` of the real entry `G i j` times
  the cast of `L(Bᵢⱼ) k`, where `Bᵢᵢ = Eᵢᵢ` and `Bᵢⱼ = Eᵢⱼ + Eⱼᵢ` for `i < j`.
  It uses `selfAdjointPart ℚ (single i j (if i = j then 1 else 2))` to construct
  those basis elements from Mathlib's symmetrization, `(A + star A) / 2`:
  the diagonal `1` is unchanged, and off the diagonal the input `2` cancels the
  factor `1/2`. This is exactly the basis convention of the node, with no lost
  factor of two. Terms with `i > j` have zero coefficient. Each entry functional
  is `(LinearMap.proj j).comp ((LinearMap.proj i).comp subtype)`, so the helper
  has type `selfAdjoint (Matrix (Fin n) (Fin n) ℝ) →ₗ[ℝ] (Fin m → ℝ)`.
  It is constructed, rather than postulated or supplied as an additional parameter.
- The premise `h` is an existential real symmetric matrix `G` with
  `(G : Matrix (Fin n) (Fin n) ℝ).PosDef` and
  `rationalSymmetricRealExtension L G = (fun k ↦ (b k : ℝ))`.
  Mathlib `Matrix.PosDef` requires symmetry (Hermitian over `ℝ`) and strict
  positivity of `∑ i,j, z_i G_ij z_j` for all nonzero finitely supported vectors.
  Because `Fin n` is finite, these are exactly all real vectors in the node.
- The conclusion gives a rational symmetric matrix `H` with the exact rational
  equation `L H = b`, and
  `((H : Matrix (Fin n) (Fin n) ℚ).map (fun q : ℚ ↦ (q : ℝ))).PosDef`.
  Thus positive definiteness is tested on the entrywise real image, exactly as
  requested; the conclusion does not approximate the equations.

Dependency declarations read and used:

- Statement dependency `def-weil-field`: Mathlib `Field`,
  `Mathlib.Algebra.Field.Defs`, through the field instances of `ℚ` and `ℝ`.
- Supporting existing Mathlib constructions: `selfAdjoint` and its module structure
  in `Mathlib.Algebra.Star.SelfAdjoint`; `selfAdjoint.submodule` and
  `selfAdjointPart` in `Mathlib.Algebra.Star.Module`; `invertibleTwo` in
  `Mathlib.Algebra.CharP.Invertible`; `Matrix.single` in `Mathlib.Data.Matrix.Basis`;
  `LinearMap.pi` and `LinearMap.proj` in `Mathlib.LinearAlgebra.Pi`;
  `Matrix.PosDef` in `Mathlib.LinearAlgebra.Matrix.PosDef`.
  Full signatures, bodies and relevant docstrings were read.
- Proof dependency `lem-sfb-rational-linear-system-parametrization`:
  `Matrix.exists_rat_affine_parametrization_of_real_solution`, module
  `Sheaf.LinearAlgebra.RationalLinearSystemParametrization`, imported privately.
  Its full signature includes arbitrary zero dimensions and a finite rational
  particular solution and homogeneous directions parametrizing every real solution.
- Proof dependency `lem-sfb-positive-definite-entrywise-neighbourhood`:
  `Matrix.posDef_entrywise_neighbourhood`, module
  `Sheaf.LinearAlgebra.PositiveDefiniteEntrywiseNeighbourhood`, imported privately.
  Its signature uses `Matrix.PosDef` and includes symmetric perturbations and `n = 0`.
- Proof dependency `lem-sfb-real-rational-interval-density`: Mathlib
  `exists_rat_btwn` in `Mathlib.Algebra.Order.Archimedean.Basic`, imported privately.
  Its full signature specializes to `ℝ` without any extra hypothesis.

The theorem docstring gives all five DAG proof steps: handle the empty matrix,
use upper-triangular coordinates and rational affine parametrization, obtain the
positive-definite neighbourhood, approximate the free parameters rationally, and
bound every entry of the perturbation while retaining the exact equations.
Milne II §1, Lemma 1.3, printed pp.77–78 was read using `pdftotext` on PDF pages
82–85. It motivates the rational algebra setting but does not assert this matrix
lemma; the module preserves the node's honest agent-auxiliary attribution.
The current blueprint unit `_section.md` at `literature/blueprint/latest/blueprint/
sec-six-functors-basics/sk-thm-sf-ctf-stability/` was also read for context.

Edge cases checked before and after drafting:

- `n = 0`: the real extension is an empty sum, hence the zero map. Its premise
  forces the real cast of `b` to be zero, hence `b = 0`. The unique empty rational
  matrix solves the equations, and all vectors are zero, so positivity is vacuous.
- `m = 0`: the right hand side and the output of either linear map are the unique
  empty vector. The theorem permits a rational identity matrix (or the empty one).
- `n = m = 0`: both previous descriptions agree, with no nonempty instance required.
- `n = 1`: the only coefficient is `L(E₀₀)`, with diagonal normalization exactly one.
- `n = 2`: for the off-diagonal entry the basis element is `E₀₁ + E₁₀`, multiplied
  once by `G 0 1`, not twice or by half that value.
- `L = 0`: the premise forces `b = 0`, and a rational positive definite matrix works.
  Inconsistent equations, such as `n = 0` with `b ≠ 0`, do not satisfy the premise.
- A unique feasible matrix, or a parametrization with no free directions, is
  included; the proof returns the rational particular solution immediately.

Searches (all on 2026-10-24):

- `msearch.py ... leanfinder`: “A rational linear map on symmetric matrices with
  rational right hand side admitting a real positive definite solution admits a
  rational positive definite solution”. Eight hits (`Matrix.PosDef.intCast`,
  `Matrix.posDef_intCast_iff`, `Matrix.PosDef.of_toQuadraticForm'`,
  `Matrix.PosDef.natCast`, `Matrix.PosDef.toQuadraticForm'`, `Matrix.PosDef.one`,
  `Matrix.posDef_natCast_iff`, `Matrix.PosDef.ofNat`); no feasibility theorem.
- `msearch.py ... leansearch`: “A rational linear system on symmetric matrices with
  a positive definite real solution has a rational positive definite solution”.
  Eight positivity/Gram/comparison hits, starting with `Matrix.PosDef`; no match.
- `msearch.py ... loogle 'Matrix.PosDef, Matrix.IsSymm'`: one hit,
  `Matrix.PosDef.of_toQuadraticForm'`, a comparison result, not this theorem.
- `msearch.py ... grep 'symmSubmodule|symmetricSubmodule|rational.*[Ff]easib'
  LinearAlgebra`: zero hits. Direct Mathlib `rg` located the existing symmetric
  matrix predicates and self-adjoint module representation used here.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id and rational
  positive/feasibility patterns found no copy of this result. The existing
  `RationalPositiveDefiniteGram` concerns decomposition of a given rational
  matrix, not feasibility for a rational linear map.
- Direct `rg` of Mathlib, both project roots and `dag/lean_names_upstream.json` for
  `rationalSymmetricRealExtension|exists_rat_posDef_of_real_solution` found no
  declaration-name collision. DAG searches located no additional symmetric-matrix
  space that needs to be introduced; Mathlib supplies the notion directly.

Validation: `scompile.py Q56 lem-sfb-rational-positive-definite-feasibility` compiled
both its sandbox and library-mode views cleanly (1.6 s and 1.5 s respectively).
All variables are explicitly bound, and `set_option autoImplicit false` enforces
this. There is exactly one postponed proof, the named theorem for this node.
No `STATEMENT-DISPUTED` issue was found.

## Second reading by Q56

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
