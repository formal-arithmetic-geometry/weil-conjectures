## Worker report

The module `Sheaf.RingTheory.PowerSeriesAdicGradientControl` states
`MvPowerSeries.adic_gradient_control`, with one `sorry` and no new definitions.
The item node changes only in `lean`. Its statement and dependency lists are unchanged.
No statement dispute, missing notion, or dependency-interface fault was found.

Clause-by-clause correspondence:

- A field of arbitrary characteristic is `(F : Type u) [Field F]`, for an explicitly
  declared universe `u`. There is no characteristic assumption or integer inverse.
- The nonnegative number of variables is `(n : ℕ)`. The series ring D is
  `MvPowerSeries (Fin n) F`; the polynomial ring P is `MvPolynomial (Fin n) F`.
  Its embedding into D is Mathlib's coefficient-preserving polynomial coercion.
- The series variable ideal is `Ideal.span (Set.range
  (X : Fin n → MvPowerSeries (Fin n) F))`. The polynomial ideal J is the analogous
  span of `MvPolynomial.X : Fin n → MvPolynomial (Fin n) F`.
- The formal series derivative is `pderiv F i`; polynomial derivatives are
  `MvPolynomial.pderiv i`. These are the dependency nodes' actual Mathlib derivations.
- For every integer s at least one, `∀ s : ℕ, 1 ≤ s → ∀ f, f ∈ ... ^ s →
  ∀ i : Fin n, pderiv F i f ∈ ... ^ (s - 1)` is the first conjunct. Natural-number
  exponents with the positivity condition cover precisely the specified integers.
- For every r at least one and every polynomial g in J^r, the second conjunct
  quantifies `r`, its positivity, `g`, and its membership in the polynomial ideal
  power. For each coordinate i it asserts that the embedded polynomial derivative
  belongs to the `(r - 1)`st series ideal power, and that it equals the series
  derivative of the embedded g. Coordinatewise membership is exactly membership
  of the polynomial gradient in the direct sum of n copies of that ideal, because
  the index set `Fin n` is finite. No separate finiteness assumption is needed.
- For every h in D and r at least one, the third conjunct uses
  `truncTotal (r + 1) h`. Its coefficient formula retains exactly total degrees
  strictly less than r+1, so this is the specified p_{r+1}(h), rather than a
  rectangular truncation or an arbitrary approximating polynomial.
- The first clause of that conjunct says `h - ↑(truncTotal (r + 1) h) ∈ ... ^ (r + 1)`.
  The next clause says for each i that the difference of their series partial
  derivatives lies in `... ^ r`. The compatibility clause identifies the derivative
  of the embedded truncation with its polynomial derivative.
- Q_r is written literally as `MvPowerSeries (Fin n) F ⧸ ... ^ r`.
  `Ideal.Quotient.mk` is its canonical quotient map and
  `KaehlerDifferential.D F Q_r` is its universal F-derivation.
  The last equality has left side `D F Q_r (Ideal.Quotient.mk _ h)` and right side
  the sum over `i : Fin n` of the quotient of `pderiv F i h` acting by scalar
  multiplication on `D F Q_r` of the quotient of `X i`. Thus coefficients live in
  Q_r and the equality lives in Ω[Q_r/F], exactly as required. It does not assert
  that formal partial derivatives descend to derivations on Q_r.

Dependency declarations read and used:

- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, its algebra structure,
  `MvPowerSeries.X`, and `MvPolynomial.toMvPowerSeries` (the canonical coercion).
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`; its recorded universal
  property is `MvPolynomial.aeval` in `.Eval` and `MvPolynomial.algHom_ext` in
  `.Basic`. The statement needs the ring and its embedding, not a new evaluation map.
- `Mathlib.RingTheory.MvPowerSeries.Derivative`: `MvPowerSeries.pderiv`, read together
  with `coeff_pderiv` and `pderiv_coe`. This is the `mathlib_match` of
  `def-trf-formal-power-series-partial-derivative`, which has no `lean` record.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `KaehlerDifferential.D`,
  and its recorded universal property `KaehlerDifferential.linearMapEquivDerivation`.
- `Mathlib.Algebra.MvPolynomial.PDeriv`: `MvPolynomial.pderiv`, with its monomial
  formula, exactly the polynomial-partial-derivative dependency.
- Proof-only import `Mathlib.RingTheory.Kaehler.Polynomial` supplies
  `KaehlerDifferential.mvPolynomialBasis`, `mvPolynomialBasis_repr_apply`, and
  `mvPolynomialBasis_apply` for the recorded polynomial differential formula.
- Proof-only import `WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients`
  supplies `power_series_mem_combined_ideal_pow_iff`, read with its full signature
  and coefficient-ideal proof docstring. All recorded proof-dependency modules are
  imported; no import-cycle omission was necessary.
- `Mathlib.RingTheory.MvPowerSeries.Trunc`: existing `MvPowerSeries.truncTotal` and
  `coeff_truncTotal_eq_ite` render the explicitly specified total-degree truncation.

Sources checked: local `literature/stacks-project/algebra.tex`, labels
`lemma-differential-mod-power-ideal` (Tag 02HQ, including its one-power Leibniz
estimate) and `lemma-differentials-polynomial-ring` (Tag 00RX, including the partial
coordinate derivations). As the node says, the full formal-series statement is
an explicit coefficient/truncation argument, not literally the statement of either tag.
The module docstring gives all four proof steps and names their DAG dependencies.

Edge cases checked mathematically before writing:

- n = 0: the only exponent is zero; D and P are F, the variable ideals are zero,
  all series are retained by the positive-degree truncation, and Ω[F/F] and the
  empty sum vanish. No nonempty-index hypothesis was introduced.
- s = 1 and r = 1: the gradient bound has target ideal power zero, namely the
  whole ring; Q_1 is F, and both sides of the finite differential identity vanish.
- Zero and constant inputs have zero derivatives and unchanged positive truncations.
- Positive characteristic, including a variable monomial of degree equal to the
  characteristic: its derivative can vanish; the coefficient formula only multiplies
  by natural-number factors and all conclusions still hold.
- No claim is made at r = 0 or s = 0, and subtraction of exponents occurs only
  under the specified positivity assumptions.

Searches (2026-10-24):

- `msearch.py ... leanfinder`: "formal partial derivatives lower powers of the
  variable ideal and compute Kahler differentials in truncated multivariate power
  series rings" returned eight hits, including
  `KaehlerDifferential.mvPolynomialBasis_repr_apply` and polynomial cotangent
  formulas. None states the full series ideal/truncation/finite-level conjunction.
- `msearch.py ... loogle`: "MvPowerSeries.pderiv, MvPowerSeries.truncTotal"
  returned zero hits.
- `msearch.py ... grep`: "truncTotal|trunc.*[Dd]eg|pderiv.*ideal|ideal.*pderiv"
  in `RingTheory/MvPowerSeries` returned fifteen hits, identifying `truncTotal`
  and approximation results, but no exact matching theorem.
- `msearch.py ... leansearch`: "formal power series partial derivative lowers
  powers of the variables ideal and gives differential formula modulo powers"
  returned eight hits on polynomial pderiv and one-variable derivatives. None
  gives the complete multivariate assertion.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `truncTotal`, and adic-gradient names found existing truncation constructions
  and `FormalRelativeDerivationExpansion`. That theorem concerns relative
  derivations along homomorphisms; it does not state this quotient universal
  differential identity with all the present clauses. Reused the existing
  truncation construction. A declaration-name/item-id search in both source
  roots and `dag/lean_names_upstream.json` found no matching declaration.

Validation: the prescribed `scompile.py` compiled the delivered file in sandbox
and library module modes without errors or warnings (13.8 s and 3.1 s respectively).
All binders and universes are explicit. The longest Lean line is below 100 characters.

## Second reading by Q42

The delivered section with this heading was the worker re-reading its own work ("This is
the worker's second pass; independent review is left to the maintainer"). The maintainer's
reviewer replaced it with the independent clause-by-clause reading below (review of
9dc99c380f43, 2026-10-24). The Lean and the node record are unchanged.

Node clauses, the Lean that renders each, and the verdict:

1. F is a field of arbitrary characteristic: `(F : Type u) [Field F]`. There is no
   characteristic, `Invertible`, or `CharZero` hypothesis. Exact.
2. n ≥ 0, D = F[[t_1,…,t_n]], P = F[t_1,…,t_n] ⊂ D: `(n : ℕ)`, `MvPowerSeries (Fin n) F`
   (def-weil-pbc-multivariate-power-series), `MvPolynomial (Fin n) F`
   (def-weil-pbc-mv-polynomial-ring). The inclusion is Mathlib's coefficient-preserving
   coercion `MvPolynomial.toMvPowerSeries`. Exact.
3. 𝔫 = (t_i) ⊂ D and J = (t_i) ⊂ P: `Ideal.span (Set.range MvPowerSeries.X)` and
   `Ideal.span (Set.range MvPolynomial.X)`, each in its own ring. Exact.
4. ∂_i on D is `MvPowerSeries.pderiv F i` (Derivative.lean:118). Its coefficient formula
   `coeff_pderiv` is (d_i+1)·coeff_{d+e_i}, as def-trf-formal-power-series-partial-derivative
   says. That node is a Mathlib leaf (mathlib_match) without a `lean` record; earlier
   landed citers use it the same way. The polynomial derivative is `MvPolynomial.pderiv i`
   (def-weil-pbc-polynomial-partial-derivative). Exact.
5. For s ≥ 1 and f ∈ 𝔫^s, ∂_i f ∈ 𝔫^{s-1} for all i: the first conjunct. The quantifiers
   are ∀ s, 1 ≤ s, ∀ f, membership, ∀ i, and the natural subtraction s-1 sits under
   1 ≤ s. Exact.
6. For g ∈ J^r with r ≥ 1, the embedded gradient lies in (𝔫^{r-1})^{⊕n}, and the
   polynomial and series derivatives agree: the second conjunct, with
   `↑(MvPolynomial.pderiv i g) ∈ 𝔫^(r-1) ∧ ↑(MvPolynomial.pderiv i g) = pderiv F i ↑g` for
   each `i : Fin n`. Membership coordinate by coordinate is membership in the finite
   direct sum. The agreement is asserted under the node's own hypotheses (it is
   `pderiv_coe` in general), so it is not weaker than the node. Exact.
7. For h ∈ D and r ≥ 1, p_{r+1}(h) collects the terms of total degree < r+1:
   `truncTotal (r + 1) h : MvPolynomial`. By `coeff_truncTotal_eq_ite` its coefficient at x
   is `if x.degree < r+1 then coeff x h else 0`. That is the specified polynomial, not a
   rectangular truncation `trunc`. Exact.
8. h − p ∈ 𝔫^{r+1} and ∂_i h − ∂_i p ∈ 𝔫^r: the first two clauses of the third conjunct.
   ∂_i p is the series derivative of the embedded polynomial; by item 6 it equals the
   polynomial derivative. Exact.
9. With Q_r = D/𝔫^r, d(h mod 𝔫^r) = Σ_i (∂_i h mod 𝔫^r)·d(t_i mod 𝔫^r) in Ω_{Q_r/F}:
   `KaehlerDifferential.D F (D ⧸ 𝔫^r) (mk h) = ∑ i, mk (pderiv F i h) • D F _ (mk (X i))`.
   The F-algebra structure on the quotient is `Ideal.Quotient.algebra`, and the scalar
   action is the Q_r-module structure of Ω[Q_r⁄F]
   (def-weil-pbc-kahler-differentials). The coefficients are taken in Q_r, and nothing
   claims that ∂_i descends to Q_r. Exact.

Mathematical check: all clauses are true over any field, as the node proof shows.
`power_series_mem_combined_ideal_pow_iff` with J = 0 gives the total-degree coefficient
criterion, and the identity in item 9 follows from q(h) = q(p) and q(∂_i h) = q(∂_i p),
using the polynomial formula pushed through the universal property.

Edge cases. n = 0: both ideals are span ∅ = ⊥, the powers with exponent ≥ 1 are ⊥, Q_r = F,
and both sides of item 9 are 0 (an empty sum; Ω[F⁄F] = 0). The clauses are stated without
a nonempty-index hypothesis. s = 1 and r = 1: the target power is ⊤, Q_1 ≅ F, and the
identity holds. Characteristic p: only natural-number factors appear, and there is no
division. r = 0 and s = 0 are excluded, as the node excludes them. Universes: one
universe u for F; Ω and the quotient live in Type u; no variable is left unbound.

One definition per notion: there are no new definitions. All objects are Mathlib
declarations recorded by the stmt_deps. `rg truncTotal` over lean/Sheaf and
lean/WeilConjectures finds FormalRelativeDerivationExpansion,
PolynomialCombinedCompletion, PowerSeriesAdicEvaluation and others, but no statement of
this assertion. The item has no existing declaration.

Gates: the module and theorem docstrings carry the source place (algebra.tex 02HQ/00RX,
agent-written argument) and `(blueprint: lem-trf-power-series-adic-gradient-control)`.
The theorem docstring has proof steps 1–4. The proof is `sorry` only. There is no
hollow definition. The node `lean.statement` matches the file signature verbatim. The
node's statement and stmt_deps are unchanged against live.
