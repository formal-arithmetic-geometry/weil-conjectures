## Worker report

The module `Sheaf.RingTheory.IsotropicCylinderOrder` states
`MvPowerSeries.isotropicCylinder_order_calculation`, with its sole proof `sorry`.
The existing node's statement, dependencies and proof are unchanged. Four helper
definitions give the constructions explicitly introduced by that statement:
`cylinderIdealOrder`, `isotropicCylinderSeries`, `isotropicCylinderIdeal`, and
`controlledCylinderIdeal`. All four contain real data, with no proof choices or
postponed theorems in their definitions. They are recorded in `lean.declarations`.
No missing independent notion, dependency repair, or statement correction is needed.

The helper `cylinderIdealOrder K J` is literally the supremum in extended naturals
of the natural numbers q such that K is contained in J^q. This is ideal order,
not the existing order of a single power series or of a stalk ideal sheaf.
`isotropicCylinderSeries k d f` applies Mathlib formal substitution
u_j -> t^k*u_j, and shifts the t coefficient index upward by k*d to construct
its quotient as a power series. `isotropicCylinderIdeal` is the span of these
images for all f in K. This construction introduces no generator choice; the
first part of the theorem equates it with the span using any finite generators.
`controlledCylinderIdeal K k d i` is the existing colon construction with the
singleton {t^(i*d)}: exactly those power series whose product with t^(i*d)
belongs to the first transformed ideal. The multiplication identity in the theorem
certifies that all of that ideal, rather than just its divisible part, is recovered.

Clause-by-clause correspondence:

- F is arbitrary in an explicit universe `u`, with `[Field F]`. The natural-number
  parameter `n` includes zero. R is `MvPowerSeries (Fin n) F`, and S is
  `MvPowerSeries (Fin (n + 1)) F`. The u variables are indexed by `Fin.castSucc`;
  `Fin.last n` is t. These are the same finite-variable power-series rings as
  the dependency. Coefficients, products and constants use Mathlib's construction.
- The finitely generated ideal is `K : Ideal R` and `hfg : K.FG`.
  `hd : 1 ≤ d` is exactly d >= 1. `hK` is containment in the d-th power of
  `Ideal.span (Set.range X)`, namely the displayed u-variable ideal.
- The definition of order is `cylinderIdealOrder`. Its supremum ranges over all
  natural q with the required containment; the codomain `ℕ∞` retains infinity.
- The first conjunct quantifies over every natural `k` with `1 ≤ k`.
  Its first clause asserts, for every `f ∈ K`, that multiplying the constructed
  power series by t^(k*d) recovers the actual substituted series. This certifies
  the quotient denoted t^(-k*d) in the node, without a field-of-fractions choice.
- Its next clause quantifies over every `g : Finset R` with
  `Ideal.span (g : Set R) = K`, and equates the span of the divided images of g
  with `isotropicCylinderIdeal K k d`. This is precisely independence of any
  finite generating set, including possible zero entries and the empty set.
- `K ≠ ⊥ → ∃ m : ℕ` gives the finite m only in the nonzero case. The equality
  `cylinderIdealOrder K (Ideal.span (Set.range X)) = (m : ℕ∞)` identifies it
  with the node's order; `d ≤ m` gives its stated lower bound. This m is fixed
  before quantifying over k and i, as in the node.
- For every k >= 1, the t-adic order uses `Ideal.span {X (Fin.last n)}` and is
  `(k*(m-d) : ℕ∞)`. The total order uses the ideal spanned by all n+1 variables
  and is `((k+1)*m-k*d : ℕ∞)`. Both subtractions take place in naturals before
  casting, justified by d <= m.
- For every natural i with `i*d ≤ k*(m-d)`, the equality
  `Ideal.span {t^(i*d)} * controlledCylinderIdeal K k d i =
  isotropicCylinderIdeal K k d` asserts that the controlled quotient is indeed
  an ideal of power series dividing the entire original ideal.
- The next two equalities give its t-adic order `k*(m-d)-i*d` and total order
  `(k+1)*m-(k+i)*d`, with the same containing ideals. The bound on i ensures
  nonnegative differences; no subtraction involving infinity occurs.
- The iff renders containment in `(t)^d` exactly as
  `(i+1)*d ≤ k*(m-d)`, with non-strict inequality and equality permitted.
- The zero clause is independent of m and any finite-order division bound.
  For each k >= 1 it asserts that the first transform is zero and that both
  its orders are top. For every i >= 0 the controlled transform is zero,
  both its orders are top, and it lies in every `(t)^q`. Thus all the displayed
  containment tests hold. At i=0, colon by {1} is the first transform itself.
- The final implication `n = 0 → K = ⊥` explicitly includes the node's last
  observation: the empty variables ideal is zero and its positive powers
  force K=0. The zero clause then applies to every i and k in that case.

Dependencies read and used:

- `def-weil-pbc-multivariate-power-series`: `Mathlib.RingTheory.MvPowerSeries.Basic`,
  declaration `MvPowerSeries`, whose complete definition is coefficient families
  `(σ →₀ ℕ) → R` with finite Cauchy products. Imported publicly through
  `Mathlib.RingTheory.MvPowerSeries.Substitution`, which also supplies `X`, `coeff`,
  and the actual `MvPowerSeries.subst` used in the construction. Read `subst`'s
  signature and docstring: it is evaluation when `HasSubst` holds. Here every
  substituted variable has constant coefficient zero and there are finitely
  many variables, so `hasSubst_of_constantCoeff_zero` applies for all k.
- Proof dependency `lem-weil-pbc-power-series-combined-ideal-coefficients`:
  `WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients`, declaration
  `power_series_mem_combined_ideal_pow_iff`, read with its full signature and
  docstring and imported with plain `import`. It is the coefficient criterion
  with coefficient ideal zero used in the natural-language proof, in n and n+1
  variables. No duplicate Sheaf twin is imported.
- Supporting Mathlib definitions: `Submodule.colon` in
  `Mathlib.RingTheory.Ideal.Colon`, `Ideal.FG` in
  `Mathlib.RingTheory.Finiteness.Defs`, and the complete lattice of extended
  naturals from `Mathlib.Data.ENat.Lattice`. The colon signature takes a set;
  the singleton in the definition means multiplication by exactly t^(i*d).

Edge cases were checked before finalizing the signature:

- K=0, including an empty generating set or any finite set of zero series:
  substitution and coefficient shifts vanish, multiplication by t is injective
  over these power series rings, and each colon quotient is zero. Every finite
  power contains it and the supremum is infinity.
- n=0: R is F, the empty variables ideal is zero, and d>=1 forces K=0;
  S still has its one variable t. No positive-rank assumption is introduced.
- m=d: the first t-order is zero; the division condition forces i=0.
  Containment in `(t)^d` is false since d>0. The total order is m.
- i=0: colon by {1} returns K_k, so both pairs of formulas agree.
- Equality i*d=k*(m-d): the controlled t-order is zero and total order is m;
  containment in the positive power `(t)^d` is false.
- Equality k*(m-d)=(i+1)*d: the t-order is exactly d and containment is true.
- k=1 and a principal monomial ideal `(u^m)`: the image is generated by
  t^(m-d)*u^m, and further division shifts the t-degree by i*d, verifying every
  numerical formula. The coefficient argument also treats nonmonomial generators
  without cancellation, since their u-exponents remain distinct.
- Arbitrary characteristic and universe u are retained. There is no
  Noetherianity, completeness, nonempty-variable, or characteristic restriction
  in the signature beyond the field and formal-series objects in the node.

Searches made on 2026-10-24:

- `msearch.py ... leanfinder "Exact orders of a formal power series ideal after
  isotropic substitution and controlled division by a power of t"`: eight hits,
  all univariate Weierstrass division/preparation. No exact statement.
- `msearch.py ... loogle "MvPowerSeries.subst, MvPowerSeries.order"`: only
  `MvPowerSeries.le_order_subst`, a lower bound for a single series, with no
  exact ideal orders, controlled quotient, or generator independence.
- `msearch.py ... grep
  "idealOrder|ideal_order|order.*subst|weightedOrder|divXPow"
  RingTheory/MvPowerSeries`: twenty hits on weighted order and substitution
  bounds. The returned signatures do not state this ideal calculation.
- `msearch.py ... leansearch "Ideal adic order and formal power series cylinder
  substitution divided by a monomial"`: eight hits on univariate divXPowOrder
  and substitution-order lower bounds. None is the multivariate ideal result.
- `rg` in Mathlib's Ideal and MvPowerSeries directories and the project's
  `lean/WeilConjectures` and `lean/Sheaf`, by order, cylinder, isotropic,
  quotient, and substitution: no matching statement or cylinder construction.
  Found `Hironaka.adicOrder` in `Sheaf.RingTheory.LocalStandardBasisInvariants`,
  which is the order of one element, not containment of an ideal; and
  `HilbertSamuel.order` in `Sheaf.AlgebraicGeometry.MarkedIdealOrder`, which is
  the order of a scheme ideal sheaf at a point, not the two displayed formal
  ideal orders. Neither supplies this node's construction or statement.
- `rg`/`grep` for the item id in `lean/WeilConjectures`: no hits. A full-name
  search for the five proposed declarations in Mathlib, both project source
  trees, and `dag/lean_names_upstream.json` had no hits.
- Read the latest blueprint's `sk-i-curve-zero/_section.md` and the ancestor
  `lem-trf-local-term-locality.proof.md` for context. The cylinder calculation
  is this agent-formulated DAG input, not a claim that the current ancestor
  proof itself spells out these formulas. The full six-step coefficient proof
  from the node is carried in the theorem docstring, and the cited BM local
  copy remains WANTED as the source record says; no unavailable text is claimed
  to have been inspected.

Validation: `scompile.py Q50 lem-trf-isotropic-cylinder-order-calculation` compiled
both its sandbox identity and `Sheaf.RingTheory.IsotropicCylinderOrder` cleanly.
One initial elaboration needed the explicit Mathlib finiteness-definitions import;
the final imports resolve it. All variables and universes are explicit and
`autoImplicit` is disabled. There are no additional postponed theorems, hollow
definitions, statement disputes, or unresolved node faults.

## Second reading by Q50

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
