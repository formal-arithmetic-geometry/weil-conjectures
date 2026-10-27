## Worker report

The module `Sheaf.FieldTheory.NonarchimedeanPrimePowerRootEstimates` states
`AbsoluteValue.nonarchimedean_prime_power_root_estimates`, with one postponed theorem
and no definitions. The node changes only in `lean`. No statement correction, new
node, or dependency repair is needed. The proof docstring reproduces the five-step
DAG proof plan, including the characteristic-two sign term and the zero cases.

Source checked: Temkin, Stable modification of relative curves,
[arXiv:0707.3953v3](https://arxiv.org/pdf/0707.3953v3), printed p. 46,
Lemma 6.2.10(i)--(ii). The PDF is absent locally, so the original PDF was opened
through the web reader. The item's difference estimate and arbitrary-root
formulation are justified by the supplied DAG proof. The current blueprint is
`literature/blueprint/latest`; searching it for the item, Lemma 6.2.10, and the
Temkin reference found no direct occurrence of this auxiliary node. Its blueprint
ancestor remains the node's recorded `lem-trf-local-term-locality`.

Hypothesis and clause correspondence:

- A field E: `{E : Type u} [Field E]`, with an explicit arbitrary universe `u`.
- A real absolute value: `(abv : AbsoluteValue E ℝ)`; Mathlib supplies
  multiplicativity, definiteness, nonnegativity and the triangle inequality.
- Nonarchimedean: `(hna : IsNonarchimedean abv)`, exactly the strong triangle
  inequality, not a condition only on the residue field.
- The valuation ring E°: `(A : ValuationSubring E)` and
  `(hA : ∀ z : E, z ∈ A ↔ abv z ≤ 1)`. This supplies the standard bundled
  Mathlib valuation ring with its underlying subset specified exactly. It is not
  an arbitrary valuation ring or an additional restriction: for every such
  nonarchimedean absolute value the closed unit ball is a valuation subring.
  Addition and multiplication preserve that ball, and a nonzero element outside
  it has inverse of absolute value below one. The membership equation uniquely
  determines A by `ValuationSubring.ext`.
- The residue field is `IsLocalRing.ResidueField A`. Its maximal ideal is precisely
  the elements with absolute value below one: an element of the closed unit ball
  is a unit exactly when its absolute value is one (its inverse then lies in the
  same ball). Thus this is exactly the quotient appearing in the node, using the
  Mathlib local-ring construction rather than a second quotient definition.
- Positive residue characteristic p: `(p : ℕ) (hp : 0 < p)` and
  `[CharP (IsLocalRing.ResidueField A) p]`. No field-characteristic-p hypothesis
  is imposed on E, and primality is a consequence, not an extra assumption.
- n ≥ 0: `(n : ℕ)`; q is everywhere the explicit natural-number power `p ^ n`.
  There is no let binder or constraint n > 0.
- t ≥ 1 and x₁,...,xₜ: `(t : ℕ) (ht : 0 < t) (x : Fin t → E)`.
  Fin t gives exactly t summands. On this nonempty finite type, the real supremum
  `(⨆ i : Fin t, abv (x i))` is the maximum in the node.
- First bound: the first conjunct is
  `abv ((∑ i, x i) ^ (p ^ n) - ∑ i, x i ^ (p ^ n)) ≤`
  `abv (p : E) * (⨆ i, abv (x i)) ^ (p ^ n)`.
  The natural power of the finite maximum agrees with the maximum of the
  natural powers, since the values are nonnegative.
- Difference bound: the second conjunct quantifies `∀ a b : E` and bounds
  `abv ((a-b)^(p^n) - (a^(p^n)-b^(p^n)))` by
  `abv (p : E) * max (abv a) (abv b) ^ (p ^ n)`.
- Every choice of roots: the last conjunct quantifies
  `∀ (ys : Fin t → E) (y : E)` with hypotheses
  `(∀ i, ys i ^ (p ^ n) = x i)` and `y ^ (p ^ n) = ∑ i, x i`.
  These imply the required bound on `abv (y - ∑ i, ys i)`; there is no existence
  assumption or selected root function, so every choice is covered.
- The p in absolute values is explicitly `(p : E)`. Both root factors on the
  right are real powers with real exponent `(1 / ((p ^ n : ℕ) : ℝ))`.
  Positive p gives p^n ≥ 1. With nonnegative bases these are exactly the
  nonnegative real roots; the reciprocal is not natural-number division.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`, supplied
  through the public statement imports. Its full declaration extends
  `CommRing K, DivisionRing K`.
- `def-trf-valuation-ring`: `ValuationRing` and `ValuationRing.TFAE`, in
  `Mathlib.RingTheory.Valuation.ValuationRing`. The latter identifies the class
  with the fraction-field membership condition. The bundled field-subring
  interface is `ValuationSubring` from
  `Mathlib.RingTheory.Valuation.ValuationSubring`, publicly imported. Its data is
  a subring with `∀ x, x ∈ A ∨ x⁻¹ ∈ A`; it carries `ValuationRing` and
  `IsLocalRing` instances. This is the same standard notion, not a private copy.
- `lem-pur-prime-power-binomial-divisibility`: `WittVector.map_frobeniusPoly.key₁`,
  `Mathlib.RingTheory.WittVector.Frobenius`; read its docstring and signature with
  `[Fact p.Prime]`, and `(n j : ℕ) (hj : j < p ^ n)`. Imported privately for
  stage 3, with j = k-1 as the node's Mathlib match specifies.
- `lem-pur-commutative-ring-binomial-expansion`: `add_pow`, in
  `Mathlib.Data.Nat.Choose.Sum`, for `[CommSemiring R] (x y : R) (n : ℕ)`.
  Imported privately for stage 3; the field specializes its assumptions.
- `lem-trf-nonarchimedean-finite-sums`: `IsNonarchimedean.apply_sum_le_sup` and
  `IsNonarchimedean.apply_sum_eq_of_lt`, in
  `Mathlib.Algebra.Order.Ring.IsNonarchimedean`. Both signatures and docstrings
  were read; the first needs a nonempty finite set, the second needs invariance
  under negation and a strict largest summand. This module is public because its
  `IsNonarchimedean` notion also appears in the statement.

Edge cases checked before writing: n=0 gives q=1 and all errors zero, including
unique prescribed first roots. t=1 permits arbitrary distinct roots and the
bound still covers their difference; it does not force root equality in mixed
characteristic. All xᵢ=0 force all chosen roots and their sum-root to vanish.
Equal characteristic p makes abv(p)=0, and Frobenius additivity and injectivity
make every error zero. Mixed characteristic and p=2 are allowed, and the
proof plan explicitly accounts for the even-power sign correction. Trivial
absolute values on positive-characteristic fields are allowed. A trivial
absolute value on a characteristic-zero field has no positive residue
characteristic and is correctly excluded by the node's hypothesis. Fields
without the stipulated roots have no obligation under the last implication.
The forbidden t=0 case is excluded exactly by ht, with no assumption excluding
n=0. No `STATEMENT-DISPUTED` fault was found.

Searches performed through the prescribed `msearch.py` (raw results are also in
sandbox searches.jsonl):

- LeanFinder: “In a nonarchimedean field of residue characteristic p, the error
  between a sum raised to p^n and the sum of p^n powers, and the error of arbitrary
  p^n roots, is bounded using the absolute value of p”. Eight hits, including
  `RingSeminorm.exists_index_pow_le`, `IsNonarchimedean.add_pow_le`, Hensel and
  p-adic approximation results. None states the three error bounds.
- Loogle: `AbsoluteValue, IsNonarchimedean, HPow.hPow`. One hit,
  `IsNonarchimedean.eval_mvPolynomial_le`, bounding homogeneous polynomial
  evaluations, not the specified errors or roots.
- Grep: `(norm|abs|apply).*(sum.*pow|pow.*sum|root.*sub)` under Analysis.
  Twenty-five unrelated norm, sum, and power hits; no exact statement.
- LeanSearch: “In a nonarchimedean field of residue characteristic p, bound the
  difference between the p^n power of a sum and the sum of the powers by the
  absolute value of p times the maximum power, and bound errors of arbitrary
  roots”. Eight hits include `sum_pow_char_pow`, `sub_pow_char_pow`,
  `add_pow_prime_pow_eq`, and general inequalities. The Frobenius identities
  require characteristic p in E, and none states the mixed-characteristic
  estimate or arbitrary-root conclusion.
- Local rg searches in Mathlib, lean/WeilConjectures and lean/Sheaf for
  `prime_power_root_estimates|nonarchimedean.*root`, and broader searches for
  prime-power errors, valuation subrings, and residue characteristic. No exact
  match or conflicting declaration name. The broader searches found existing
  p-adic-specific modules and Mathlib's valuation/residue-field interfaces.
- The exact item-id search in lean/WeilConjectures and in
  dag/lean_names_upstream.json returned no match.

Validation: prescribed `scompile.py` passed in sandbox and library module modes,
with no compiler errors or warnings. No direct compiler, Lake build, shared-clone
write, or shared-clone git command was used.

## Second reading by Q87

A separate pass reopened the node and the complete final module. It checked all
three conjuncts against the displayed node formulas, the field and absolute-value
binders, the exact valuation-ring membership equation, positive *residue*
characteristic, the natural exponents, nonempty finite indexing, and the real
reciprocal root exponents. The maximum and root parentheses match the node.
The root quantifiers precede both root equations, so the conclusion applies to
every family of roots and never asserts existence. No mathematical mismatch was
found, and no statement change was made. The independent review is the
maintainer's review, as specified by the dispatcher; no other agent was started.
