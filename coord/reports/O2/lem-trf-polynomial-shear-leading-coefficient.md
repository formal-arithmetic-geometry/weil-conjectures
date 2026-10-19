## Worker report

The module `lean/Sheaf/TraceFormula/PolynomialShearLeadingCoefficient.lean`
states `Algebra.exists_polynomial_shear_leading_coefficient` with proof `sorry`.
It uses `m : ℕ` and `MvPolynomial (Fin (m + 1)) R`; this is the node's
`n ≥ 1` presentation with `m = n - 1`, and `m = 0` is exactly the `n = 1`
case. The exponent family `e : Fin m → ℕ` is the list
`e₁, …, e_{n-1}`, and `∀ i, 0 < e i` renders positivity. The hypothesis
`hg : ¬ ∃ r : R, g = MvPolynomial.C r` says precisely that `g` is outside the
constant-polynomial map.

The conclusion has witnesses `d : ℕ`, `a : R`, and
`b : Fin d → MvPolynomial (Fin m) R`; `0 < d` renders positive degree,
and `∃ ν, MvPolynomial.coeff ν g = a ∧ a ≠ 0` says that `a` is a nonzero
coefficient of the original polynomial. For `i : Fin (m + 1)` below the last
index, `Fin.castPred i h` selects the corresponding first-variable index,
and `Fin.castSucc` embeds it back into `Fin (m + 1)`. Thus the `MvPolynomial.aeval`
argument sends that variable to
`X_i + X_last^(e_i)` and sends the last variable to itself. The right side is
`C a * X_last^d` plus the finite sum over `j : Fin d` of the lifted coefficient
`MvPolynomial.rename Fin.castSucc (b j)` times `X_last^j`; `Fin d` is exactly
`0 ≤ j < d`. This gives every clause of the displayed node formula, including
the empty exponent list when `m = 0`.

The sole dependency is the Mathlib record of
`def-weil-pbc-mv-polynomial-ring`: `MvPolynomial` from
`Mathlib.Algebra.MvPolynomial.Basic`, `MvPolynomial.aeval` from
`Mathlib.Algebra.MvPolynomial.Eval`, and the uniqueness operation
`MvPolynomial.algHom_ext` from `Basic`. The module additionally imports
Mathlib's existing `MvPolynomial.rename` and `Fin` predecessor/successor
operations; no project notion is copied or redefined.

Edge cases checked before writing the statement were `m = 0` (one variable,
empty exponent family and identity substitution), a single nonconstant
monomial, a polynomial with a nonzero constant term, vectors differing only
in the last coordinate, and rings with zero divisors (the statement only
requires a nonzero coefficient and never assumes it is a unit). The zero ring
has no polynomial satisfying `hg`, so it introduces no exceptional witness
case. The finite sum over `Fin d` is empty only when `d = 0`, excluded by
`0 < d`.

Searches for an existing statement or definition found no exact match:

- `msearch.py N2 lem-trf-polynomial-shear-leading-coefficient leanfinder
  "Triangular polynomial substitution over a commutative ring gives a nonzero
  scalar leading coefficient"` returned eight unrelated leading-coefficient
  and Weierstrass-curve results; no triangular substitution theorem.
- `msearch.py ... loogle "MvPolynomial.aeval, MvPolynomial.rename,
  leadingCoeff, NoetherNormalization"` returned zero hits (Loogle rejected
  `leadingCoeff` as an unknown identifier).
- `msearch.py ... grep "varChange|polynomial.*shear|leadingCoeff"
  RingTheory/NoetherNormalization.lean` found only private field-specific
  helpers at lines 107 and 124–131, not this arbitrary-ring statement.
- `rg` over `WeilConjectures/` and the project's `lean/Sheaf/` found no
  declaration named for this item and no helper-polynomial or triangular
  shear statement. Existing nearby mentions concern different geometric
  arguments.

No `STATEMENT-DISPUTED` flag or node fault was found.

## Second reading by N2

I reread the node, its Stacks 051N/051M proof steps, and the module signature
after compilation. The commutative-ring hypothesis, nonconstant hypothesis,
positive exponents, positive `d`, nonzero original coefficient, lower-variable
coefficient family, exact substitution, and `n = 1` identity case are all
present. The only presentational change is the definitionally equivalent
`m + 1` indexing, which makes the first-variable ring `Fin m` and avoids an
extra predecessor-size hypothesis. The `Fin.castPred`/`Fin.castSucc` transports
ensure that both sides live in the same `MvPolynomial (Fin (m + 1)) R`.
No mismatch or omitted clause was found.
