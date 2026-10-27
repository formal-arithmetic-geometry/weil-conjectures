## Worker report

The module `Sheaf.RingTheory.FormalRelativeDerivationExpansion` states
`MvPowerSeries.formal_relative_derivation_expansion` with one `sorry` and no new
definitions. It preserves the live node's entire natural-language statement,
statement dependencies, accepted split, and proof dependencies. No statement
correction or dependency repair is needed.

The inherited BLOCKED ending concerned a stage-1 split already accepted for Q54.
The current `coord/brief-stage2.md` §0 explicitly distinguishes that from this
stage-2 assignment. The live node is split and reviewed, without a Lean record;
this delivery adds only that record and its statement module.

Write `a` for `Ideal.span (Set.range (MvPowerSeries.X : Fin m →
MvPowerSeries (Fin m) F))` and `b` for the corresponding expression with `r`.
These are explanatory names in this report only; the signature spells them out.
Write `H` for `(MvPowerSeries.truncTotal N h : MvPowerSeries (Fin m) F)`.
The existing Mathlib `truncTotal` retains exactly the coefficients of degree
strictly less than `N`, by `coeff_truncTotal_eq_ite`. Its polynomial-to-series
coercion is the canonical embedding, so this is precisely the stated `H_N`.

Every hypothesis and clause is rendered as follows:

| Node text | Lean rendering |
| --- | --- |
| F is a field | `(F : Type u) [Field F]`, with explicit universe `u` |
| m,r are nonnegative integers, including zero | `(m r : ℕ)`, without positivity assumptions |
| S=F[[t_1,…,t_m]], T=F[[z_1,…,z_r]] | `MvPowerSeries (Fin m) F` and `MvPowerSeries (Fin r) F`; indexing starts at zero with no mathematical change |
| Variable ideals a and b | The canonical ideal spans of the ranges of `MvPowerSeries.X`, fully written out |
| ψ is an F-algebra homomorphism | `ψ : MvPowerSeries (Fin m) F →ₐ[F] MvPowerSeries (Fin r) F` |
| ψ(a)⊆b | `hψ : ∀ f, f ∈ a → ψ f ∈ b`, exactly the elementwise inclusion |
| E is F-linear | `E : MvPowerSeries (Fin m) F →ₗ[F] MvPowerSeries (Fin r) F` |
| Relative Leibniz rule | `hE : ∀ f g, E (f * g) = ψ f * E g + ψ g * E f` |
| Termwise formal partial derivative | The dependency's `MvPowerSeries.pderiv F j` |
| E(a^N)⊆b^(N−1) for N≥1 | The first conjunct is `∀ N, 1 ≤ N → ∀ f, f ∈ a ^ N → E f ∈ b ^ (N - 1)` |
| All subsequent estimates for every h and N≥1 | The second conjunct starts `∀ (h : MvPowerSeries (Fin m) F) (N : ℕ), 1 ≤ N → …` |
| h−H_N∈a^N | First inner conjunct: `h - H ∈ a ^ N` |
| ∂_j(h−H_N)∈a^(N−1), every j | Second inner conjunct: `∀ j : Fin m, pderiv F j (h - H) ∈ a ^ (N - 1)` |
| E(h−H_N)∈b^(N−1) | Third inner conjunct: `E (h - H) ∈ b ^ (N - 1)` |
| ψ(∂_j(h−H_N))∈b^(N−1), every j | Fourth inner conjunct: `∀ j : Fin m, ψ (pderiv F j (h - H)) ∈ b ^ (N - 1)` |
| E(H_N)=Σ_j ψ(∂_j H_N)E(t_j) | Fifth inner conjunct: `E H = ∑ j : Fin m, ψ (pderiv F j H) * E (X j)` |
| E(h)−Σ_j ψ(∂_j h)E(t_j)∈b^(N−1) | Sixth inner conjunct: `E h - ∑ j : Fin m, ψ (pderiv F j h) * E (X j) ∈ b ^ (N - 1)` |
| Intersection over N≥0 of b^N is zero | Third outer conjunct: `(⨅ N : ℕ, b ^ N) = ⊥` in the ideal lattice |
| Exact identity for every h | Last conjunct: `∀ h, E h = ∑ j : Fin m, ψ (pderiv F j h) * E (X j)` |
| All assertions include m=0 and r=0; empty sum is zero | All bounds quantify independently of `j`; only the derivative clauses quantify over `Fin m`. No `Nonempty` or positive-dimension assumptions occur. Mathlib's finite sum over `Fin 0` is zero. |

The bounds not involving `j` are deliberately outside the quantifiers over `Fin m`.
Thus none becomes vacuous when there are no source variables. Natural subtraction
is used only under `1 ≤ N`, exactly rendering `N−1`.

Dependency declarations read and used:

- `def-weil-pbc-multivariate-power-series`: `MvPowerSeries`, recorded module
  `Mathlib.RingTheory.MvPowerSeries.Basic`, with its actual coefficient-family
  definition and canonical ring/algebra structures. Public import.
- `def-trf-formal-power-series-partial-derivative`: Mathlib leaf
  `MvPowerSeries.pderiv` in `Mathlib.RingTheory.MvPowerSeries.Derivative`.
  Read its complete derivation definition, coefficient formula, and variable
  formulas. Public import; no duplicate derivative construction.
- Proof dependency `lem-weil-pbc-power-series-combined-ideal-coefficients`:
  `power_series_mem_combined_ideal_pow_iff` in
  `WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients`.
  Read its full signature and proof docstring. Plain proof-only import, preferring
  the recorded upstream module over its retired Sheaf twin.
- `Mathlib.RingTheory.MvPowerSeries.Trunc`: `MvPowerSeries.truncTotal`, canonical
  polynomial embedding, and `coeff_truncTotal_eq_ite`. Public import for the
  truncation in the signature. These are existing Mathlib notions; no helper node
  is necessary.

Source checked: `literature/stacks-project/curves.tex`, Tag 0C4B,
`lemma-fitting-ideal-well-defined`, especially its final coordinate-change
paragraph. The source invokes the chain rule and omits details; this node's
accepted agent-written auxiliary argument supplies them. The latest blueprint
ancestor `lem-trf-local-term-locality` and its proof were also read. They concern
contracting local terms, as the accepted split report already notes; this delivery
preserves the inherited auxiliary ancestry without claiming a formal-coordinate
paragraph appears in that latest ancestor.

Edge cases checked before drafting:

- `m=0`: the source consists of constants. Leibniz gives `E(1)=0` and linearity
  gives `E=0`; every positive-degree truncation is the whole series. Derivative
  quantifiers are empty, both displayed sums are zero, and the remaining bounds
  are still asserted.
- `r=0`: the target variable ideal is zero. Zeroth powers are the whole ring,
  and positive powers are zero. Point derivations can have nonzero values on source
  variables; the statement allows them. For example evaluation at zero with
  `E(h)` its linear coefficient satisfies the identity and the filtration bounds.
- `N=1`: all exponents `N−1` equal zero. The source-tail claim still says that
  the tail has no constant term. `H_1` is constant, so its derivative and its E-image
  are zero. The unrestricted target bounds are correct, rather than omitted.
- Positive characteristic p: a term `t^p` has zero partial derivative and E-image
  by repeated Leibniz; no characteristic-zero or separability assumption is used.
- One variable and `ψ(t)=z²`: `E(h)=ψ(h')c` obeys the relative Leibniz rule and
  gives the required bounds for arbitrary target series c. This checks the
  direction of ψ and the multiplication by E(t).
- No continuity assumption was added: the finite Leibniz bound yields exactly the
  needed control before taking the separated limit.

Searches for an exact existing statement (2026-10-23):

- `msearch.py … leanfinder`, query “A relative derivation along a local algebra
  homomorphism between finite variable formal power series rings lowers powers
  of the variable ideal by one and is the sum of partial derivatives times its
  values on variables”: eight hits, including `MvPolynomial.mkDerivation_monomial`,
  `MvPolynomial.mkDerivationₗ_monomial`, `Derivation.apply_aeval_eq'`, and
  `KaehlerDifferential.mvPolynomialBasis_repr_comp_D`. These have polynomial
  source or state differential primitives; none gives the series and adic claims.
- `msearch.py … leansearch`, query “A relative derivation of multivariate formal
  power series is determined by its values on the variables using total degree
  truncations and the separated variable ideal filtration”: eight hits including
  `MvPolynomial.derivation_ext`, `MvPolynomial.mkDerivation`,
  `MvPowerSeries.trunc'`, and `PowerSeries.derivative`. No complete match.
- `msearch.py … loogle`, query `MvPowerSeries.pderiv, MvPowerSeries.truncTotal`:
  zero hits for the joint pattern.
- `msearch.py … grep`, pattern
  `relative.*deriv|deriv.*trunc|deriv.*ideal|chain.rule` in
  `RingTheory/MvPowerSeries`: five hits in `Derivative.lean` concerning
  `trunc_pderiv`, not a relative-derivation expansion.
- `rg` of both project roots `lean/WeilConjectures` and `lean/Sheaf`, patterns
  `formalRelativeDerivationExpansion|formal_relative_derivation_expansion|relative_derivation|lem-trf-formal-relative-derivation-expansion`:
  no declaration or blueprint-id match. Broader relative/derivation searches
  found unrelated relative differentials and derived-category material.
- Read the full Mathlib partial-derivative API and total-degree truncation
  definition; they supply the notions used but not this conjunctive theorem.

Validation: the required `scompile.py` compiled both the sandbox statement and
its library module on the live server, cleanly (1.1 s and 1.2 s respectively).
All variables and the sole universe are explicitly bound. No diagnostic commands,
local notation, local instances, or private declarations occur. The sole postponed
proof has the accepted five-step natural-language proof in its docstring.

No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
