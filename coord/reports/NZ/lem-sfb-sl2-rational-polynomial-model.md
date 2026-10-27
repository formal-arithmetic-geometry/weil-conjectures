## Worker report

The module `Sheaf.RepresentationTheory.Sl2RationalPolynomialModel` states
`RepresentationTheory.exists_sl2_rational_polynomial_model`, with its entire proof
postponed by `sorry`. It defines no new notions. The item's accepted stage-1 split,
statement, proof, and dependency lists are preserved; only `lean` is added to its node.
The inherited unchanged-item refusal concerned stage 1. The current queue lists this
item at stage 2, and it has no Lean record or repair note in the read clone.

Clause-by-clause correspondence:

- A rational vector space `W` of arbitrary universe is `(W : Type u) [AddCommGroup W]
  [Module ℚ W]`; finite dimension is `[FiniteDimensional ℚ W]`. No nonzero-space
  hypothesis is imposed.
- The three rational endomorphisms are `(E F H : Module.End ℚ W)`. Multiplication in
  this ring is composition in the order used in `HE - EH`.
- `hHE`, `hHF`, and `hEF` render respectively `HE - EH = 2E`,
  `HF - FH = -2F`, and `EF - FE = H`. Scalars 2 and -2 are explicitly rational.
- `hE : IsNilpotent E` and `hF : IsNilpotent F` are precisely the two nilpotence
  assumptions.
- `hH` asks for a basis `b : Module.Basis (Fin d) ℚ W` and integral weights
  `weight : Fin d → ℤ`, with `H (b j) = (weight j : ℚ) • b j`.
  This is exactly diagonalizability with integer eigenvalues. A finite-dimensional
  diagonalizable operator has a finite eigenbasis; requiring integer entries of that
  basis is equivalent to requiring all its eigenvalues to be integers. Multiplicities
  and repeated weights are permitted; no particular basis or dimension is fixed.
- The polynomial space `P_n` is the existing
  `MvPolynomial.homogeneousSubmodule (Fin 2) ℚ n`. Its ambient ring is precisely
  `MvPolynomial (Fin 2) ℚ`, with `X = MvPolynomial.X 0`, `Y = MvPolynomial.X 1`.
  Mathlib defines this submodule by support in monomials of total degree n. For two
  variables these exponent pairs are exactly `(n-i,i)`, `0 ≤ i ≤ n`, so its basis
  is the node's `X^(n-i) Y^i`, not a symmetric-power quotient or an abstract copy.
- `∃ (r : ℕ) (n : Fin r → ℕ)` is a finite index set and its nonnegative degrees.
  Every finite set can be enumerated by `Fin r`, so this presentation adds no
  restriction. The cardinality is existential, not an extra hypothesis on W.
- `T : W ≃ₗ[ℚ] DirectSum (Fin r) (fun i ↦ ... (n i))` is the required rational
  linear isomorphism to the actual direct sum of polynomial subspaces.
- For every w and component i, the three conjuncts state the underlying-polynomial
  equalities `T(Ew)_i = X * pderiv Y (Tw_i)`,
  `T(Fw)_i = Y * pderiv X (Tw_i)`, and
  `T(Hw)_i = X * pderiv X (Tw_i) - Y * pderiv Y (Tw_i)`.
  Equality after all projections and the injective subtype inclusions is precisely
  each requested intertwining equality. The differential expressions preserve total
  degree: each derivative lowers one exponent and the variable multiplier restores
  it. Stating their underlying values avoids any extra restricted-operator definition
  or postponed well-definedness lemma. These are exactly the specified operators.
- `r = 0` is allowed. `Fin 0` is empty and its direct sum is the zero module, so the
  assertion for W = 0 is retained without a nonempty-instance constraint.

Dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` in
  `Mathlib.Algebra.MvPolynomial.Basic`, imported through the public Mathlib polynomial
  imports. Its definition is the additive monoid algebra on finitely supported
  exponent vectors. Also read `MvPolynomial.algHom_ext` in Basic and
  `MvPolynomial.aeval` in Eval, verifying the dependency's universal-property clauses.
- `def-weil-pbc-polynomial-partial-derivative`: `MvPolynomial.pderiv` in
  `Mathlib.Algebra.MvPolynomial.PDeriv`, a derivation over the coefficient ring.
  Read its full declaration, monomial formula and values on variables.
- Existing auxiliary API: `MvPolynomial.homogeneousSubmodule` and
  `MvPolynomial.IsHomogeneous` in `Mathlib.RingTheory.MvPolynomial.Homogeneous`;
  `DirectSum` and its component function in `Mathlib.Algebra.DirectSum.Basic` and
  `.Module`; `FiniteDimensional` in `Mathlib.LinearAlgebra.FiniteDimensional.Defs`.
- The proof-only dependency `lem-sfb-sl2-invariant-complement` currently has no Lean
  record. Its full statement was read; it is referenced in the proof docstring.
  There is no import to add for it yet. It is not needed to elaborate this statement.
  Stage-2 rule 7 requires imports only for proof dependencies that are already stated.

Sources read: the local Milne PDF was converted to text in the sandbox, and Example
22.33 (printed p.472) and Theorem 23.70 with proof (a) (printed pp.507–508) were read.
The theorem invokes Weyl semisimplicity over a characteristic-zero field; the example
uses homogeneous binary forms. The node specifies the differential convention
directly. For group substitution this corresponds to transpose substitution
`g·p(X,Y) = p(aX+cY,bX+dY)`; an upper unipotent yields `p(X,Y+tX)`, whose derivative
is `X ∂/∂Y`. No group action or integral-lattice assertion is substituted for the
node's rational endomorphism statement.

Edge cases checked before writing: W = 0 uses an empty eigenbasis and empty output
sum; n = 0 consists of constants, so all three differential operators are zero;
n = 1 has E(Y) = X, F(X) = Y and H(X) = X, H(Y) = -Y, verifying all three signs
and composition orders. Repeated trivial summands give the zero action in every
dimension. Both endpoint derivatives have zero coefficient. There is no bound on
degrees, no algebraic-closure or faithfulness hypothesis, and no universe relation
restricting W. No statement fault or STATEMENT-DISPUTED issue was found.

Searches (2026-10-24), through the required msearch wrapper:

- LeanFinder: `Every finite dimensional rational sl2 module is a direct sum of
  homogeneous polynomial representations`: eight hits, including
  `IsSl2Triple.HasPrimitiveVectorWith`, its `exists_nat`, weight-space decomposition
  for nilpotent Lie algebras, and a special adjoint-root-space result; no match to
  the complete polynomial-model statement.
- LeanSearch: `Finite dimensional rational sl2 representations decompose as
  homogeneous binary polynomials`: eight hits, including `Polynomial.homogenize`,
  `MvPolynomial.decomposition`, and a primitive-vector weight formula. None states
  the requested decomposition of an arbitrary rational sl2 module.
- Loogle: `IsSl2Triple, LieModule`: nine hits about primitive vectors and highest
  weight strings. None supplies this direct sum and its polynomial intertwiner.
- Loogle: `MvPolynomial.homogeneousSubmodule`: twelve hits; the existing homogeneous
  submodule API is used directly rather than duplicated.
- Wrapper grep: `homogeneousSubmodule|polynomial.*model|IsSl2Triple` in Algebra:
  sixteen sl2-triple and root-system hits, no polynomial-model theorem.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `rationalPolynomialModel`, `sl2.*[Pp]olynomial`, and `[Pp]olynomial.*sl2`: no match.
  Searching `homogeneousSubmodule` finds existing uses of the same Mathlib space,
  not an alternative binary-form model. The full new declaration name was also
  searched in Mathlib, both project roots, and `dag/lean_names_upstream.json` without
  a collision. No duplicate definitions or new helper nodes are needed.

## Second reading by NZ

This is the worker's final clause audit; no independent agent was started, as the
dispatcher explicitly forbids it and the maintainer independently reviews delivery.
Re-read the node alongside the file: all three rational commutators, both nilpotence
assumptions, and the integral eigenbasis condition occur as separate binders; each
target polynomial subspace is a subtype of the specified two-variable polynomial
ring. The first component identity differentiates with respect to Y and multiplies
by X; the second differentiates with respect to X and multiplies by Y; the third has
the X term positive and Y term negative. Projection and subtype injectivity make
these exactly the three map identities. `Fin r`, with r existential and possibly
zero, represents an arbitrary finite direct sum. The monomial indexing and the
degree-zero and empty-space cases were checked above. No mismatch required changing
the accepted natural-language statement or proof split.
