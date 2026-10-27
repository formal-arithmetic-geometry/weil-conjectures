## Worker report

The module `Sheaf.RingTheory.SupportedFormalDivision` states
`MonomialDiagram.exists_unique_supported_formal_division`. Its only theorem proof
is `sorry`. No definitions, new nodes, dependency modules or statement corrections
are needed. The node is unchanged except for `lean` and two additional already
landed statement dependencies, `def-trf-formal-initial-diagram` and
`def-trf-supported-homogeneous-division`, whose definitions are reused.

Hypothesis and clause correspondence:

- The coefficient field is `{L : Type u} [Field L]`, with arbitrary explicit
  universe `u`. The numbers of variables and divisors are `{n s : ℕ}`. The series
  are `MvPowerSeries (Fin n) L`, precisely the recorded power-series definition.
- `G : Fin s → MvPowerSeries (Fin n) L` indexes the ordered finite list, starting
  at zero in Lean. `α : Fin s → Fin n →₀ ℕ` indexes its initial exponents.
  `hα : ∀ i, IsFirstExponent (G i) (α i)` says their coefficients are nonzero
  and all earlier coefficients vanish. Thus it includes both nonzeroness of
  each divisor and the specification of its least exponent. There is no extra
  standard-basis, distinctness, ordering-of-the-divisors or ideal hypothesis.
  Quantification over a specified first exponent is the usual binder form of
  “let αᵢ be the least exponent”; no initial exponent is chosen from an
  unproved existence assertion.
- `IsFirstExponent` uses `Finsupp.DegLex (· < ·) (· < ·)`. Its source definition
  compares `Finsupp.degree` first, then `Finsupp.Lex`. The latter compares the
  first differing coordinate in the ascending order on `Fin n`. This is exactly
  ascending lexicographic order on (total degree, α₁, ..., αₙ).
- The node's orthant αᵢ + Nⁿ is `{e | α i ≤ e}` in the componentwise partial
  order. Assigning its exponent to the first containing orthant gives
  `quotientSupport α i = {β | ∀ j < i, ¬ α j ≤ α i + β}`. This is Δᵢ exactly,
  since αᵢ ≤ αᵢ + β automatically. The union of the Eᵢ is the union of these
  orthants, namely `generated α`. Hence E₀ is `(generated α)ᶜ`. Intermediate
  Eᵢ do not need separate declarations.
- `F` is arbitrary. `∃ Q R` quantifies over the full quotient family and
  remainder in the same series ring. The first conjunct is
  `F = (∑ i : Fin s, Q i * G i) + R`.
- The next conjuncts are `Function.support (Q i) ⊆ quotientSupport α i`
  and `Function.support R ⊆ (generated α)ᶜ`. A series is literally a function
  on exponents, and its evaluation is definitionally `MvPowerSeries.coeff`;
  `Function.support` means nonzero value. This is the node's coefficient support.
- The explicit `∀ Q' R'` clause assumes just the same decomposition and support
  conditions and concludes `Q' = Q ∧ R' = R`. This is joint uniqueness of all
  quotients and the remainder, not merely uniqueness among solutions satisfying
  some additional bound.
- The `∀ q : ℕ` clause assumes coefficient vanishing for `β.degree < q` in F.
  It concludes the identical vanishing in R, and coefficient vanishing in Qᵢ
  for `β.degree < q - (α i).degree`. Natural truncated subtraction makes this
  condition empty when the bound is not positive, exactly as the node requires.
  The estimates hold for every q for the same decomposition.
- The last clause `s = 0 → R = F` states the empty-divisor conclusion explicitly.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field (K : Type u)`, extending `CommRing K`
  and `DivisionRing K`; the recorded match of `def-weil-field`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries (σ : Type*) (R : Type*)`
  is `(σ →₀ ℕ) → R`; `coeff` is `LinearMap.proj`. The multiplication is the
  existing finite-convolution ring structure, not a replacement.
- `Sheaf.RingTheory.FormalInitialDiagram`: `MonomialDiagram.IsFirstExponent`.
  Read its full docstring and signature. It uses the exact ascending degree-lex
  order and excludes the zero series by a nonzero initial coefficient.
- `Sheaf.RingTheory.SupportedHomogeneousDivision`:
  `MonomialDiagram.generated` and `MonomialDiagram.quotientSupport`. Read their
  full definitions and docstrings. These definitions accept arbitrary indexed
  families; no `IsOrderedVertexFamily` hypothesis is used here. Its polynomial
  homogeneous division predicate is not substituted for formal division.

The original two proof dependencies are exposed through the power-series import;
there are no additional recorded proof dependencies. The theorem docstring gives
all nine coefficient-recursion proof steps, including their dependency citations.
The current blueprint's locality statement and proof were read in
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`.
That current route uses contracting correspondences. This item belongs to the
historical local-presentation branch explicitly retained in its DAG record.
The node says BM 1997 is WANTED; its proof is honestly agent-written, not a
claimed quotation from an available source. No source-based correction is needed.

Edge cases checked mathematically before writing:

- `s = 0`: the sum and quotient family are empty, generated α is empty, and
  R = F, with exactly the original degree bound.
- `n = 0`: there is only the empty exponent. If s > 0, the first nonzero scalar
  divisor takes that exponent, so Q₀ = F/G₀, all later quotients and R vanish.
- Repeated initial exponents and an orthant covered by earlier orthants produce
  empty quotient supports, forcing those quotients to be zero; they are allowed.
- A unit divisor has initial exponent zero; its first available orthant fills
  the complement of earlier ones. No positivity assumption on initial degrees
  is present.
- `F = 0` has all quotients and R zero by uniqueness. `q = 0` makes all degree
  conditions vacuous. `q ≤ |αᵢ|` makes only the corresponding quotient bound
  vacuous, while the remainder bound remains in force.
- Every field characteristic and every coefficient universe is allowed.

Searches for an existing theorem (2026-10-24):

- `msearch.py ... leanfinder "unique multivariate formal power series division
  quotients remainder supported disjoint initial monomial cones"`: eight hits,
  including `MonomialOrder.div`, `div_single`, `div_set` (polynomial division)
  and univariate Weierstrass division; none is this theorem.
- `msearch.py ... loogle "MvPowerSeries, MonomialOrder.degLex, support"`:
  zero hits, unknown identifier `support` reported by the service.
- `msearch.py ... grep "degLex|degreeLex|division|remainder"
  RingTheory/MvPowerSeries`: one unrelated `map_eq_zero` hit.
- `msearch.py ... leansearch "formal power series unique division disjoint
  support cones degree bounds"`: eight hits, mainly univariate Weierstrass
  division, coefficient shifts, and polynomial support. No exact match.
- `rg` for `supportedFormal|formalDivision|supported.formal|degLex|degreeLex`
  in `lean/WeilConjectures` and `lean/Sheaf`: no exact theorem; found the
  generic-monotone-diagram consumer. The required search for the item id in
  `lean/WeilConjectures` returned no matches.
- Focused source searches found `MonomialOrder.degLex`, the existing
  `IsFirstExponent`, `generated` and `quotientSupport` definitions. Their full
  source definitions were read; no new versions were introduced.
- `rg` for the proposed full theorem's last name in `lean/WeilConjectures`,
  `lean/Sheaf` and `dag/lean_names_upstream.json`: no collision.

Validation: `scompile.py Q62 lem-trf-supported-formal-division` compiled the module
both as a sandbox file (3.4 s) and at its library module path (4.0 s), exit zero,
with no diagnostics. The report below records a fresh clause-by-clause rereading.

## Second reading by Q62

Reread the original node, the completed module and the imported definition bodies.
The field, arbitrary n and s, ordered divisor indexing, nonzero minimal initial
coefficients, degree-lex order, arbitrary F, decomposition, both support
containments, joint uniqueness, uniform degree estimates and explicit empty-family
case all correspond as detailed above. In particular I checked that the uniqueness
premises do not assume degree estimates, and that the degree subtraction is in
natural numbers, so no unwanted hypothesis is imposed when q ≤ |αᵢ|. The initial
exponents may coincide: only index order is used by quotientSupport. The parent
consumer needs exactly remainder support outside the union of vertex orthants,
which is what the statement gives. No mismatch or statement fault was found and
no change was made during this rereading. This is a second pass by the same worker;
the dispatcher prohibits starting other agents, and the maintainer performs the
independent delivery review.
