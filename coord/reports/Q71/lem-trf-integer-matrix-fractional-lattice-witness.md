## Worker report

The module `Sheaf.LinearAlgebra.IntegerMatrixFractionalLatticeWitness` states
`Matrix.integer_fractional_lattice_witness`, with its entire proof `sorry`.
The mathematical statement and dependency lists are unchanged. No new notions,
definition nodes, dependency modules, or statement corrections are needed.

Hypothesis and clause correspondence:

- The integer `r ≥ 1` is `(r : ℕ) (hr : 1 ≤ r)`. Indices are `Fin r`, representing
  the same r coordinates as the paper's indices 1 through r.
- The integer square matrix is `(A : Matrix (Fin r) (Fin r) ℤ)`; its nonsingularity
  is `(hA : A.det ≠ 0)`, using the dependency's exact determinant.
- Its columns in rational space are `fun j : Fin r ↦ fun i : Fin r ↦ (A i j : ℚ)`.
  The first conjunct is `LinearIndependent ℚ` of this family. This assertion precedes
  the quantification over y, so it holds even when the outside-span case is empty.
- Every integer vector is covered by `∀ y : Fin r → ℤ`. Being outside the integer
  span is `¬ ∃ m : Fin r → ℤ, A.mulVec m = y`: the i-th component of the product
  is the finite sum of `A i j * m j`, exactly an integer combination of columns.
- The coordinate vector is `∃ b : Fin r → ℚ`. The next conjunct is
  `(A.map (Int.castRingHom ℚ)).mulVec b = (fun i ↦ (y i : ℚ))`, namely Ab=y in Q^r.
- Uniqueness is stated for every solution of that equation, explicitly:
  `∀ b' : Fin r → ℚ, ...mulVec b' = ... → b' = b`. It is not merely uniqueness
  among solutions satisfying the subsequent remainder properties.
- The node's z is always the actual integer vector `fun i ↦ ⌊b i⌋`.
  The next conjunct explicitly gives both floor bounds for every coordinate:
  `(⌊b i⌋ : ℚ) ≤ b i ∧ b i < (⌊b i⌋ : ℚ) + 1`.
- The node's a is always `fun i ↦ b i - (⌊b i⌋ : ℚ)`. The node's x is always
  `y - A.mulVec (fun i ↦ ⌊b i⌋)`, formed in `Fin r → ℤ`, so its integrality
  is enforced by its type. These concrete terms are expanded in the statement,
  in accordance with the stage rule against statement-local let bindings.
- The equality x=Aa is the equality of the componentwise rational cast of this
  integer x with the rational matrix-vector product applied to this exact a.
- The following conjunct states `y - A.mulVec (fun i ↦ ⌊b i⌋) ≠ 0` in Z^r.
  Along with the preceding equality and the injectivity of Z→Q, this is exactly
  x=Aa≠0.
- Every coefficient satisfies `0 ≤ b i - (⌊b i⌋ : ℚ) ∧ b i - (⌊b i⌋ : ℚ) < 1`.
  The final existential `∃ j : Fin r, ...` asserts both strict bounds `0 < a j < 1`.

Dependency declarations read and used:

- `def-weil-pbc-matrix-determinant`: `Matrix.det`, module
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, signature and Leibniz docstring
  read at lines 45–64. This is publicly imported, as are the standard
  `LinearIndependent` and rational `FloorRing` interfaces used by the signature.
- Proof dependency `lem-weil-pbc-matrix-adjugate-identity` is a Mathlib match:
  `Matrix.adjugate_mul` and `Matrix.mul_adjugate`, module
  `Mathlib.LinearAlgebra.Matrix.Adjugate`, full signatures read at lines 264–272.
  Its module is a plain proof import. The docstring records all four proof steps
  of the node, including the two-sided rational inverse, uniqueness, floor
  bounds for negative coordinates, and nonvanishing of the integral remainder.
- The source was read in `literature/stacks-project/algebra.tex`, lines 2670–2700.
  Its adjugate identity supports the inverse construction. As the node says,
  the fractional-coordinate refinement is supplied by its DAG proof, not a
  verbatim assertion of Stacks Tag 07DQ.

Edge cases checked before drafting:

- Rank zero is excluded by the explicit bound; singular matrices are excluded by hA.
- For r=1, A=(2), y=1, one has b=1/2, z=0, a=1/2, x=1.
- For r=1, A=(2), y=-1, b=-1/2 has floor -1, a=1/2, x=1. Thus the construction
  uses floor rather than truncation toward zero.
- For A=(-2), y=1, b=-1/2, z=-1, a=1/2, x=-1; no sign condition on det is needed.
- For A=[[2,1],[0,1]] and y=(0,1), b=(-1/2,1), z=(-1,1), a=(1/2,0), x=(1,0).
  Some fractional coefficients can vanish, while at least one must be positive.
- Unimodular A has no integer vector outside its span; the y assertion is then
  vacuous, but the independent-column conjunct remains. y=0 is in the span and
  is correctly excluded. If all a_i vanished, y=Az would contradict the hypothesis.

Searches made using the prescribed msearch.py wrapper:

- LeanFinder query: "For a nonsingular integer matrix and an integer vector outside
  its integer column span, subtract floors of its unique rational coordinates to
  get a nonzero integer vector with fractional coefficients in [0,1)". Eight hits,
  including `ZSpan.fract`, `ZSpan.fractRestrict`, `ZSpan.floor`, and
  `ZSpan.fract_mem_fundamentalDomain`; none states all the matrix-specific clauses.
- LeanSearch query: "For a nonsingular integer matrix an integer vector outside its
  column span has a unique rational coordinate vector whose fractional part
  represents a nonzero integer point". Eight hits, principally the same ZSpan API,
  plus Siegel's lemma; no exact match.
- Loogle query: `ZSpan.fract_mem_fundamentalDomain`. One hit. Its full type assumes
  a supplied basis in a normed space and states membership in the fundamental
  domain, rather than this node's full integer-matrix assertion.
- Mathlib grep query: `fract_mem_fundamentalDomain|repr_fract_apply|fract_apply`,
  subdirectory `Algebra/Module/ZLattice`. Five hits in Basic.lean. The definitions
  and signatures at lines 125–195 were read: they do not themselves assert the
  unique rational coordinates and integral nonzero remainder under these hypotheses.
- Project rg query: `fractional.lattice|fractionalLattice|integerMatrix|fract_mem_fundamentalDomain|fractional_lattice`
  across `lean/WeilConjectures` and `lean/Sheaf`, and literal node-id grep in
  `lean/WeilConjectures`: no matches. A broader floor/mulVec/LinearIndependent
  search in existing matrix/lattice modules found unrelated matrix presentations
  and rank results, no exact statement.

No statement fault or disputed clause was found. The prescribed scompile.py
compiled both the sandbox and library-path forms successfully, without errors
or unexpected warnings.

## Second reading by Q71

Author's separate self-check, with the node and completed module open; the
maintainer provides the independent delivery review. I checked each clause
against the correspondence above. The rational vectors are columns (`A i j`,
not `A j i`); the outside-span condition uses integer coefficients; existence
and uniqueness concern exactly Ab=y; and the floors and remainder are fixed
constructions, not freely chosen witnesses. All casts of x and A used in x=Aa
land in Q. Nonvanishing is imposed on the actual integral x. Both non-strict
lower bounds and strict upper bounds appear for every a_i, and the last index
has both strict bounds. Independence is unconditional on y. All binders are
explicit, the proof import is non-public, and the theorem docstring contains
the source and all four steps. No mismatch or further change was found.
