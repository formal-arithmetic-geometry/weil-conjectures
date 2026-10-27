## Worker report

The module `Sheaf.RingTheory.HomogeneousQuotientCumulativeGrowth` states
`MvPolynomial.exists_polynomial_cumulative_growth_of_homogeneous_ideal` with `sorry`.
It has no new definitions or helper theorems. Only the item's `lean` field changes.
The source was read in `literature/stacks-project/algebra.tex`, lines 13853–13983:
00JZ integrates numerical polynomials; 00K1/00K2 give graded-piece eventual
polynomiality; 00K3 gives the degree drop. The node is their cumulative version.

Clause-by-clause correspondence:

- The field is `{k : Type u} [Field k]`, with unrestricted coefficient universe `u`.
- The number of variables is `{d : ℕ} (hd : 1 ≤ d)`. Natural numbers encode precisely
  the positive integer values of d in the node; `Fin d` labels its d indeterminates.
- The polynomial ring P is `MvPolynomial (Fin d) k`, the recorded dependency's ring.
- `I : Ideal (MvPolynomial (Fin d) k)` is an ideal of P; `hne : I ≠ ⊥` is nonzeroness,
  and `hproper : I ≠ ⊤` is properness.
- `hhom` says for each `f ∈ I` and each natural degree j that
  `MvPolynomial.homogeneousComponent j f ∈ I`. This is exactly the node's
  componentwise definition of homogeneity, with no extra generation condition.
- P_j is Mathlib's `MvPolynomial.homogeneousSubmodule (Fin d) k j`.
  Its source identifies it with polynomials supported on total-degree-j monomials.
- M is the actual ideal quotient P/I. The canonical map to it is
  `(Ideal.Quotient.mkₐ k I).toLinearMap`. The displayed `Submodule.map` of P_j
  is exactly M_j, the image requested in the node. These existing constructions
  are written inline, without creating another definition of a graded quotient piece.
- `DirectSum.IsInternal (fun j ↦ ...)` asserts that the canonical summation map
  from the direct sum of those actual M_j into P/I is bijective. This is the
  displayed decomposition `M = ⊕ M_j`, as a conclusion rather than a hypothesis.
- The next conjunct, `∀ j, Module.Finite k (...)`, states finite dimensionality
  of every M_j. Over a field this is Mathlib's finite-dimensional vector space notion.
- `∑ j ∈ Finset.range n, Module.finrank k (...)` is precisely h_I(n), summing
  degrees 0 through n−1. The cast to ℚ compares that integer with polynomial evaluation.
- `∃ Q : Polynomial ℚ` supplies the rational polynomial, `Q ≠ 0` its nonzeroness,
  `0 < Q.leadingCoeff` strict positivity, and `Q.natDegree < d` the strict degree bound.
  Since Q is nonzero, `natDegree` is its ordinary degree, including degree zero.
- `∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ... = Q.eval (n : ℚ)` states eventual
  equality at every integer n≥N. Because N≥1, every integer in question is a natural
  number; this loses no integer cases and does not assert equality at n=0.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (mathlib leaf).
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial`,
  `Mathlib.Algebra.MvPolynomial.Basic`; its `MvPolynomial.aeval` in `.Eval` and
  `MvPolynomial.algHom_ext` in `.Basic` were also read for the recorded universal property.
- `def-weil-vector-space-dimension`: `Module.finrank`,
  `Mathlib.LinearAlgebra.Dimension.Finrank`.
- `def-weil-polynomial-ring`: `Polynomial`, `Mathlib.Algebra.Polynomial.Basic`, with
  `Polynomial.natDegree` and `Polynomial.leadingCoeff` in `.Degree.Defs`, and `eval`.

Additional existing Mathlib APIs: `MvPolynomial.homogeneousSubmodule` and
`homogeneousComponent` in `Mathlib.RingTheory.MvPolynomial.Homogeneous`,
`Ideal.Quotient.mkₐ` in `Mathlib.RingTheory.Ideal.Quotient.Operations`,
`Submodule.map`, and `DirectSum.IsInternal` in `Mathlib.Algebra.DirectSum.Basic`.
Their types and docstrings were read; `DirectSum.Module` exposes the sum API.

The already stated proof dependencies are imported privately:
`WeilConjectures.RingTheory.GradedAlgebra.Standard` (`GradedAlgebra.IsStandard`),
`Sheaf.RingTheory.StandardGradedHilbertFunction`
(`GradedAlgebra.IsStandard.exists_eventually_eq_polynomial`),
`WeilConjectures.Mathlib.Algebra.Group.ForwardDiff`
(`Polynomial.exists_degree_lt_eval_eq_of_sub`),
`Mathlib.LinearAlgebra.Dimension.RankNullity`
(`Submodule.finrank_quotient_add_finrank`), and
`Mathlib.Analysis.Polynomial.Basic` (`Polynomial.isEquivalent_atTop_lead`).
The domain instance for `MvPolynomial` comes from its public Basic import.
The ForwardDiff dependency's abbreviated record lacks a module field; its actual
published declaration was located and read in the named upstream source module.
No dependency interface repair is needed. The theorem docstring records all eight
proof steps, including the zero degree-piece polynomial and constant cumulative case.

Edge cases checked mathematically before writing:

- d=1 and I=(T^e), e≥1: M_j has dimension one for j<e and zero otherwise;
  h_I(n)=min(n,e), so Q is the positive constant e, degree 0<1, with N=e.
- d=2 and I=(xy): dimensions are 1 in degree zero and 2 in each positive degree;
  h_I(n)=2n−1 for n≥1, degree 1<2.
- d=2 and I=(x²,y²): dimensions are 1,2,1,0,...; eventual Q=4 is allowed.
- n=1 includes the degree-zero piece; no off-by-one sum or assertion at n=0.
- The zero ideal would have cumulative degree d and is excluded by hne.
  The whole ideal would have zero cumulative polynomial and is excluded by hproper.
- No characteristic assumption is imposed on k; the polynomial takes values in ℚ,
  not k, so arbitrary positive characteristic is retained. No algebraic closure is assumed.

Searches performed (batch2 `msearch.py`, group Q109, item id):

- LeanFinder: “For a nonzero proper homogeneous ideal in a polynomial ring over a
  field the cumulative Hilbert function is eventually a nonzero polynomial of positive
  leading coefficient and degree below the number of variables”: eight hits, principally
  Chevalley degree bounds and `Polynomial.hilbertPoly`; none states the item.
- Loogle: `MvPolynomial.homogeneousSubmodule, Module.finrank`: no hits.
- Mathlib grep: `hilbertPoly|finrank.*homogeneous|homogeneous.*finrank` in RingTheory:
  five hits, all in `Polynomial/HilbertPoly.lean`. Read its module docstring and API:
  it treats coefficients of p/(1−X)^d; graded-module Hilbert polynomials are still TODO.
- LeanSearch: “Cumulative dimensions of homogeneous pieces of a nonzero proper
  homogeneous polynomial quotient are eventually a positive-leading rational polynomial
  of degree smaller than the number of variables”: eight hits for homogeneous components
  and homogenization, no cumulative-growth theorem.
- `rg -n` on both `lean/WeilConjectures` and `lean/Sheaf` with
  `homogeneous.*[Cc]umulative|cumulative.*[Hh]ilbert|homogeneousQuotient|homogeneous_quotient`:
  no exact theorem; found projective-cone cumulative function and general homogeneous
  quotient pieces. Read those: their hypotheses and purposes differ, and this delivery
  defines neither again.
- `rg -n` for the item id in `lean/WeilConjectures`: no match.
- `rg -n` in `dag/lean_names_upstream.json`, `lean/Sheaf/RingTheory`, and
  `lean/WeilConjectures/RingTheory` for
  `quotient.*cumulative|exists_polynomial.*homogeneous|exists.*cumulative`: no match.

No statement dispute, node fault, new node, dependency repair, or statement correction.

## Second reading by Q109

A separate rereading by the same worker checked the node and completed Lean side by side;
no independent worker was started, in accordance with the dispatcher's prohibition.
The maintainer's independent delivery review remains required. This rereading checked
all binders (field, d≥1, nonzero, proper, componentwise homogeneous), the actual quotient
images, their internal direct sum, finite-dimensionality, the range ending at n−1,
nonzero Q, positive leading coefficient, strict degree bound, and N≥1 with all n≥N.
No mismatch was found. In particular the finite-dimensionality and direct-sum clauses
are conclusions, and Q may have degree zero; no nonzero eventual degree-piece polynomial
is assumed. No changes resulted from this second pass.
