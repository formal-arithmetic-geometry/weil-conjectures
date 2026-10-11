## Worker report

The module defines `AlgebraicGeometry.symmetricProductPolynomial`, the integer
polynomial `F_j` used as a coordinate of the later symmetric-product morphism.
The source checkout did not include the untracked Stacks TeX or blueprint Markdown;
I checked the cited Stacks Project Tag 0A4F at
https://stacks.math.columbia.edu/tag/0A4F and the complete DAG statement.

Clause mapping:

- `n ≥ 1`: `(n : ℕ) (_hn : 0 < n)`.
- The ring `ℤ[x₁,y₁,...,xₙ,yₙ]`: `MvPolynomial (Fin n ⊕ Fin n) ℤ`.
  `Sum.inl i` indexes `x_i`; `Sum.inr i` indexes `y_i`.
- `F_0,...,F_n`: `(j : Fin (n + 1))` indexes exactly these coefficients.
- `∏ (x_i t + y_i) = ∑ F_j t^j`: the definition takes `.coeff j` of
  `∏ i : Fin n, Polynomial.C (MvPolynomial.X (Sum.inl i)) * Polynomial.X +
  Polynomial.C (MvPolynomial.X (Sum.inr i))`.
- The subset expansion follows by specializing `Finset.prod_add` to these
  polynomial factors and collecting terms of degree `j`; this is the recorded
  Mathlib match of `lem-weil-pbc-product-linear-forms-coefficients`.
- `F_0 = ∏ y_i` and `F_n = ∏ x_i` are the empty and full subset cases of
  that expansion. Each term selects one variable from each pair, so each
  monomial has multidegree `(1,...,1)`.
- For every commutative ring `R'` and `a_i,b_i ∈ R'`, `MvPolynomial.aeval`
  sends the variables to those elements; polynomial coefficient commutes with
  this evaluation, giving the coefficient of `∏ (a_i t + b_i)`.
- The formula in projective coordinates is the name of a later morphism,
  constructed in `lem-weil-pbc-symmetric-product-properties`; this node says
  explicitly that it defines only `F_j`, so no scheme parameter or morphism
  belongs to this definition. The Stacks source indexes its `F_j` in reverse.

Dependencies: `def-pc-scheme` maps to `Mathlib.AlgebraicGeometry.Scheme`,
`AlgebraicGeometry.Scheme` (read in `Mathlib/AlgebraicGeometry/Scheme.lean`);
it is used only in the node's pointer to the later morphism.
`lem-weil-pbc-product-linear-forms-coefficients` maps to `Finset.prod_add`
in `Mathlib.Algebra.BigOperators.Ring.Finset` (read in
`Mathlib/Algebra/BigOperators/Ring/Finset.lean`). The coefficient construction
uses Mathlib's `Polynomial.C`, `Polynomial.X`, `Polynomial.coeff`, and
`MvPolynomial.X` directly. No proof or `sorry` is introduced.

Edge cases: `n = 0` is excluded by `_hn`; `n = 1` gives `F_0 = y_0` and
`F_1 = x_0`; `j = 0` and `j = n` are present. The integer coefficient ring
allows evaluation in every commutative ring, including the zero ring and any
characteristic. The scheme `S` may be empty because the polynomial definition
does not depend on it.

Searches: `msearch leanfinder "coefficients of product of pairs of
indeterminates x_i t + y_i as multivariate polynomials"` found general
`MvPolynomial.coeff_mul` results, no matching definition;
`msearch loogle "MvPolynomial.esymm, Polynomial.coeff"` found
`MvPolynomial.prod_X_add_C_coeff`, the monic specialization;
`msearch grep "prod_X_add_C_coeff|esymm|symmetricProduct" RingTheory`
found the monic Vieta and elementary symmetric polynomial files, no paired
homogenized coefficient definition. `rg` over Mathlib AlgebraicGeometry and
RingTheory found no symmetric-product morphism or paired coefficient definition.
`rg` over `WeilConjectures` and `lean/Sheaf` found only prose about the
symmetric-product morphism. Searching `dag/lean_names_upstream.json` and
`WeilConjectures` for this item's name found no declaration.

## Second reading by K1

I read the sandbox node and Lean module, the signatures of both statement
dependencies, and the proof of Stacks Etale Cohomology Lemma 0A4F in
`etale-cohomology.tex`, lines 18586-18603. The source assumes only a scheme
`S` and `n >= 1` here; it uses reverse indexing, with `F_0` the leading
coefficient. The node deliberately uses ascending powers of `t`.

- `n >= 1`: `(n : ℕ) (_hn : 0 < n)` is the same restriction. Verdict: exact.
- The integer polynomial ring in the paired variables: the return type
  `MvPolynomial (Fin n ⊕ Fin n) ℤ`, with `Sum.inl i` for `x_i` and
  `Sum.inr i` for `y_i`, has precisely `2*n` independent variables.
  Verdict: exact up to the harmless zero-based names of `Fin n`.
- `F_0,...,F_n`: `(j : Fin (n + 1))` covers exactly these `n+1`
  indices, including both endpoints. Verdict: exact.
- `∏ (x_i*t+y_i) = ∑ F_j*t^j`: the body takes `.coeff j` of the
  product of `Polynomial.C (MvPolynomial.X (Sum.inl i)) * Polynomial.X +
  Polynomial.C (MvPolynomial.X (Sum.inr i))`. Thus it defines the
  unique coefficient specified by the node, with its ascending indexing.
  Verdict: exact. The full sum identity is a consequence of this definition,
  not an additional datum in the definition's type.
- The subset formula, endpoint formulas, and multidegree `(1,...,1)`:
  these are stated in the declaration docstring. They follow from the
  coefficient definition via the dependency `Finset.prod_add`; they are
  mathematical properties of this defined object, not extra inputs to it.
  Verdict: the definition denotes the claimed polynomials. This stage-2
  module does not add theorem declarations for these consequences.
- Evaluation in every commutative ring: integer coefficients in the return
  type allow the unique map `ℤ →+* R'`; coefficient evaluation commutes with
  this map. The module docstring states the clause. Verdict: the definition
  is universal for every such `R'`, with no characteristic restriction.
- The projective-coordinate formula and scheme `S`: the node expressly
  defers construction of `σ_n` to
  `lem-weil-pbc-symmetric-product-properties` (c). Accordingly neither
  `S` nor a morphism is an argument or result of this polynomial definition.
  Verdict: exact boundary. The `def-pc-scheme` dependency is Mathlib's
  `AlgebraicGeometry.Scheme`, not a competing notion.

Edge cases: `n=0` is excluded exactly as in the node and Stacks passage;
`n=1` gives `F_0=y_0` and `F_1=x_0`; `j=0` and `j=n` are in the `Fin`
index. The construction uses no nonzero-ring hypothesis, so the zero ring
and every characteristic are allowed on evaluation. An empty scheme imposes
no restriction on the polynomial definition. All indices are finite and
there is no universe parameter or implicit universe restriction.

Independent searches: `msearch leanfinder "homogeneous coefficients product
linear binary forms variables"` returned general multivariate polynomial
coefficient and quadratic-form declarations, no matching definition;
`msearch loogle "Polynomial.coeff, MvPolynomial.X, Finset.prod"` returned
`MvPolynomial.prod_X_add_C_coeff`, the monic specialization;
`msearch grep "binary form|multihomogeneous|symmetricProductPolynomial"`
found only resultant documentation. `rg` in Mathlib's multivariate-polynomial
sources, `WeilConjectures`, and the repository's `lean/Sheaf` found no
definition of these paired coefficients. I checked the dependency source:
`Finset.prod_add` expands the product of sums, while `Scheme` is the
Mathlib scheme type.

Mismatches found: none. Changes to Lean and the node: none. The existing
signature equals `lean.statement` verbatim. The single-file compile passed
without errors or warnings.
