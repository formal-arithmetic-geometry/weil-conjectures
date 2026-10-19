## Worker report

The module `Sheaf.Algebra.Polynomial.ReciprocalPolynomial` states
`Polynomial.reciprocal_polynomial_of_constantCoeff_one` with one whole-proof `sorry`.
It introduces no definition. The source is the reciprocal-polynomial display, monicity
assertion and reciprocal-root convention in
`literature/blueprint/master/blueprint/sec-zeta-weil/sk-thm-rh/prop-arithmetic-roots.md`.
I also read the corresponding current `main-20261015` statement; these parts agree.
The declaration docstring carries all six steps of the node's proof.

Hypotheses and conclusions, clause by clause:

- The arbitrary commutative ring is `{R : Type u} [CommRing R]`; the polynomial is
  `(P : R[X])`. The coefficient sequence is Mathlib's `P.coeff`. We eliminate the
  definitional notation `r = deg P`, writing `P.natDegree` everywhere, and write
  `P.leadingCoeff = P.coeff P.natDegree` for `c_r`.
- The constant coefficient assumption is `(h0 : P.coeff 0 = 1)` and the nonzero top
  coefficient is `(hr : P.leadingCoeff ≠ 0)`. This last assumption implies `P ≠ 0`
  and excludes the zero ring, without adding an instance hypothesis.
- The displayed definition of `P^#` is the existing `P.reverse`, not a new object:
  `Polynomial.reverse` is `reflect P.natDegree P`, and `coeff_reverse` gives exactly
  the coefficients `c_(r-j)` for `j ≤ r`. For `j > r`, `revAt r j = j` and the original
  coefficient vanishes. Hence this is exactly the finite sum in the node.
- Clause 1 is `P.reverse.Monic`, `P.reverse.natDegree = P.natDegree`, and
  `P.reverse.eval 0 = P.leadingCoeff`. Because the leading coefficient assumption
  excludes the zero polynomial and the zero ring, natural degrees give the stated
  degrees, including degree zero.
- Clause 2 quantifies over `∀ (K : Type v) [Field K] (φ : R →+* K)` with the sole
  additional hypothesis `φ P.leadingCoeff ≠ 0`. Its three assertions are
  `(P.map φ).natDegree = P.natDegree`, `(P.map φ).eval 0 = 1`, and
  `P.reverse.map φ = (P.map φ).reverse`. The source's injective-map and characteristic-zero
  integer-map examples explain sufficient conditions for this same hypothesis;
  they are not restrictions on `φ`. No injectivity or characteristic hypothesis is added.
- Clause 3's root equivalence, including `x = 0`, is
  `∀ x : K, (P.reverse.map φ).IsRoot x ↔ x ≠ 0 ∧ (P.map φ).IsRoot x⁻¹`.
  Mathlib `IsRoot` is exactly evaluation equal to zero. Its right side and the
  involutivity of inversion identify precisely the inverse roots and imply every
  reciprocal root is nonzero. Ordinary roots are also nonzero by the constant term one.
- The explicitly stated equivalent evaluation formula is separately retained as
  `∀ x : K, x ≠ 0 → (P.reverse.map φ).eval x =
  x ^ P.natDegree * (P.map φ).eval x⁻¹`.
- The value and nonvanishing at zero are retained as the final two conjuncts:
  `(P.reverse.map φ).eval 0 = φ P.leadingCoeff` and
  `(P.reverse.map φ).eval 0 ≠ 0`.

Dependency declarations read and used:

- `def-weil-polynomial-ring`: `Mathlib.Algebra.Polynomial.Basic`, `Polynomial`;
  degree and leading coefficient from `Mathlib.Algebra.Polynomial.Degree.Defs`,
  `Polynomial.natDegree` and `Polynomial.leadingCoeff`.
- `def-weil-polynomial-coefficient`: its Mathlib match `Polynomial.coeff` in
  `Mathlib.Algebra.Polynomial.Basic`.
- `def-weil-field`: its Mathlib match `Field` in `Mathlib.Algebra.Field.Defs`.
- `def-weil-coefficientwise-extension`: its Mathlib match `Polynomial.map` in
  `Mathlib.Algebra.Polynomial.Eval.Defs`. The recorded specialization to integers
  and an adic field uses precisely this map; here the node explicitly quantifies
  over a general `φ`, so the same existing declaration supplies that general operation.
- `def-weil-polynomial-root`: its Mathlib match `Polynomial.eval₂` and the recorded
  equivalent same-field `Polynomial.eval` / `Polynomial.IsRoot` in
  `Mathlib.Algebra.Polynomial.Eval.Defs`.
- The theorem also uses the existing `Polynomial.reverse` and `Polynomial.Monic`.
  The single polynomial public import transitively provides the polynomial dependencies;
  the field definition is publicly imported explicitly.
- The recorded proof dependency `lem-weil-integers-injective-char-zero` is supplied
  by its Mathlib match `Int.cast_injective`; its module
  `Mathlib.Data.Int.Cast.Lemmas` is a non-public proof import. All other proof
  dependencies are the same Mathlib definition modules already available above.

Edge cases checked before writing:

- `r = 0`: the polynomial is `1`, its reverse is `1`, both degrees are zero, both
  values at zero are `1`, neither polynomial has a field root, and the nonzero
  evaluation identity reads `1 = x^0 * 1`.
- The zero ring and zero polynomial cannot satisfy the nonzero leading coefficient
  hypothesis; no extraneous nontriviality assumption is necessary.
- `x = 0` is included in the root equivalence and excluded only from the division
  formula, exactly as in the node.
- Rings with zero divisors are permitted. Noninjective maps are permitted whenever
  the top coefficient survives. For example, reduction `ℤ → 𝔽₃` and `P = 1 + 2X`
  qualify; reduction to `𝔽₂` does not, and indeed would lower the degree.
- No splitting or algebraic-closure assumption is imposed; fields of any
  characteristic are covered. The independent universes `u` and `v` permit all
  coefficient rings and target fields, with no equality constraint.

Searches made (all read-only):

- `msearch.py ... leansearch "reciprocal polynomial reverse monic constant coefficient
  one inverse roots"`: eight hits, including `Polynomial.reverse`,
  `Polynomial.eval₂_reverse_eq_zero_iff` and `Polynomial.reverse_leadingCoeff`;
  no declaration gives all three clauses of this node.
- `msearch.py ... leanfinder "A polynomial with constant coefficient one has a monic
  reverse polynomial and roots are inverses after coefficientwise mapping to a field"`:
  eight hits including `eval₂_reverse_eq_zero_iff`, `eval₂_reverse_mul_pow`, and
  `eval₂_reflect_mul_pow`; no exact whole-statement match.
- `msearch.py ... loogle "Polynomial.reverse, Polynomial.map"`: zero hits.
- `msearch.py ... grep
  "reverse_map|reflect_map|eval₂_reverse|reverse_leadingCoeff|reverse_natDegree"
  Algebra/Polynomial`: eight displayed hits, including `reflect_map` and the reversal
  degree API. I read the full local `Reverse.lean` definitions and relevant signatures.
- `rg -n "reciprocal|reverse_map|eval₂_reverse|reverse.*monic|monic.*reverse"` in
  upstream `WeilConjectures/` and side `lean/Sheaf/`: the upstream
  `Polynomial.reverse_map` assumes injectivity; `roots_reverse_of_monic` assumes
  monicity and splitting; the normalized-Gauss file contains a private monicity
  helper only. None states this node. Side sources have no matching declaration.
- `rg -n "lem-weil-reciprocal-polynomial"` in upstream `WeilConjectures/`: no hits.
  The id and chosen declaration name have no match in `dag/lean_names_upstream.json`.
- `rg -n "reciprocal_polynomial_of_constantCoeff_one"` in Mathlib, upstream,
  `lean/Sheaf/` and the upstream name index: no hits before writing.

No new nodes, dependency modules, statement correction or disputed statement.
Only the item's `lean` record changes in its JSON copy.

## Second reading by N9

This is the author's second pass with the node and Lean file open; the dispatcher
brief forbids starting another agent, and the maintainer supplies independent review.
I checked that the field quantifier follows the three ring-only conjuncts, so those
conclusions do not require any map to a field. I matched the three assertions in
clause 2, the unconditional root equivalence, the conditional evaluation identity,
and both assertions about evaluation at zero. The signature uses `P.leadingCoeff`
only where the node writes `c_r`, with `r` uniformly expanded to `P.natDegree`.
There are no `let` binders, auto-bound variables, private definitions or local notation.
The ordinary-root inverse description follows exactly from the universal `IsRoot`
equivalence; no roots or field characteristics are excluded. I checked that
`Polynomial.reverse_map` was not used to smuggle in an injectivity assumption.
No mismatch found and no statement change was needed.
