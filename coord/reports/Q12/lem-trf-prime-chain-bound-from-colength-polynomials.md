## Worker report

The module `Sheaf.RingTheory.PrimeChainBoundFromColengthPolynomials` states
`IsLocalRing.primeChain_bound_of_colength_polynomials` with `sorry` as its entire proof.
It also constructs `IsLocalRing.quotientPowerColength`, the explicitly introduced
function H_I(n) of this same node. This helper has real data: the Mathlib length of
the double quotient, with the image of the original maximal ideal, and introduces no
independent mathematical notion needing a new node. Both declarations are listed in
`lean.declarations`. Only the item's `lean` field changes. No statement correction,
new node, dependency repair, disputed statement, or source fault was needed.

Source read: Stacks Project `algebra.tex`, Tag 00KQ, `proposition-dimension`, in particular
the final paragraph beginning “Assume d(R) = d”, and the recorded eight-step conditional
proof. The conditional shifted-difference hypothesis is precisely the node's extracted
version of that argument; no unconditional Hilbert--Samuel theorem is used in its place.

Hypothesis and object correspondence:

- `R : Type u` and `[CommRing R]` give the commutative ring, `[IsNoetherianRing R]`
  gives Noetherianity, and `[IsLocalRing R]` gives locality and nonzeroness. The Mathlib
  class extends `Nontrivial R`, so a redundant separate assumption is unnecessary.
- The maximal ideal m is `IsLocalRing.maximalIdeal R`. The helper uses `R ⧸ I`
  for A_I, `(maximalIdeal R).map (Ideal.Quotient.mk I)` for m_I, its natural power
  for m_I^n, and `Module.length (R ⧸ I)` for length over A_I, not over R.
- Properness is `I ≠ ⊤`. `hfinite` requires `quotientPowerColength I n < ⊤` for
  every proper I and every `n : ℕ` with `1 ≤ n`, including n = 1. No assumption is
  made at n = 0. The helper is defined there merely to make it a total function.
- `Q : Ideal R → Polynomial ℚ` supplies the polynomials. `hpoly` constrains only
  proper ideals: `Q I ≠ 0` and `0 < (Q I).leadingCoeff`. Q's unused value at top
  imposes no extra mathematical condition: a family indexed only by proper ideals
  extends by the zero polynomial at top, and restriction recovers the given family.
  Every Q in a conclusion is evaluated at a proper ideal (in particular p + (x)
  is contained in m). There is no constraint or conclusion about Q at top.
- `hpoly` then gives an individual `∃ N : ℕ, 1 ≤ N` and equality for every `n ≥ N`:
  `((quotientPowerColength I n).toNat : ℚ) = (Q I).eval (n : ℚ)`.
  Positivity of N merely places the eventual assertion in the given domain n ≥ 1;
  thresholds may vary with I. Finiteness makes `toNat` the exact finite length.
- `hdiff` quantifies over every ideal p with `p.IsPrime`, every x belonging to m
  and not to p, and some `c : ℕ` with `1 ≤ c`. Its assertion applies to every
  `n : ℕ` with `c < n`. J is exactly `p ⊔ Ideal.span {x}`. The inequality is H_J(n)
  bounded by H_p(n) minus H_p(n-c), using the finite lengths' `toNat` values.
  Natural subtraction agrees with ordinary integer subtraction here: n-c ≥ 1,
  both lengths are finite, and H_p(n-c) ≤ H_p(n) by the canonical quotient
  surjection. The quotient uses the image of m, exactly as in the statement.

Conclusion correspondence, in conjunction order:

- Every pair of proper ideals I, I' with `I ≤ I'` satisfies
  `(Q I').natDegree ≤ (Q I).natDegree`.
- For every prime p and x in m outside p, `1 ≤ (Q p).natDegree` and
  `(Q (p ⊔ Ideal.span {x})).natDegree ≤ (Q p).natDegree - 1` hold together.
  Nonzero polynomials have the stated ordinary natural degree.
- For every proper I and every `s : LTSeries (PrimeSpectrum (R ⧸ I))`,
  `s.length ≤ (Q I).natDegree`. LTSeries uses strict inclusion of prime ideals;
  its length counts inclusions, so it includes chains with a single prime (length 0).
- `ringKrullDim R ≤ ((Q ⊥).natDegree : WithBot ℕ∞)` states exactly the particular
  dimension bound for the zero ideal, with the full extended Krull dimension.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` and `isNoetherianRing_iff_ideal_fg` (lines 194–206).
- `def-weil-pbc-module-length`: its `mathlib_match` is `Module.length`,
  `Mathlib.RingTheory.Length` (lines 30–36); finite length is also characterized by
  `Module.length_ne_top_iff`. No dependency module is needed when `lean` is null:
  the recorded Mathlib match supplies the exact notion.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim`,
  `Mathlib.RingTheory.KrullDimension.Basic` (lines 27–31). Also read
  `Order.krullDim` in `Mathlib.Order.KrullDimension` (lines 70–79) and `LTSeries`
  in `Mathlib.Order.RelSeries` (lines 865–869): the supremum is over chain lengths.
- `def-weil-polynomial-ring`: `Polynomial` from `Mathlib.Algebra.Polynomial.Basic`
  (lines 73–82), `natDegree` and `leadingCoeff` from
  `Mathlib.Algebra.Polynomial.Degree.Defs` (lines 44–57), and `eval` from
  `Mathlib.Algebra.Polynomial.Eval.Defs` (lines 249–251).
- Proof dependency `lem-weil-pbc-local-ring-unit-criterion`:
  `IsLocalRing.notMem_maximalIdeal`, `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`
  (lines 79–84), imported as a proof import. The other proof dependencies are
  the same length, polynomial, and dimension definition modules already public.

Edge cases checked before writing:

- A field has only the zero proper ideal, H(n) = 1, Q = 1, and degree 0; there is
  no x in m outside a prime, and every prime chain has length 0.
- For a nonzero Artinian local ring the colength polynomials are eventually constant;
  the degree-zero case forbids a strict adjacent pair of primes. For example
  k[ε]/(ε²) has H_(0)(n) = 2 for n ≥ 2, and H_(ε)(n) = 1.
- For k[[t]], H_(0)(n) = n and H_(t)(n) = 1. Choosing x = t and c = 1 gives
  `1 ≤ n - (n-1)`, and the degree drop is from 1 to 0. More generally x of order a
  has H_(x)(n) = min(n,a), and c = a gives the required inequality for n > c.
- n = c+1 leaves n-c = 1, within the finiteness hypothesis. n = 0 is never required
  by a hypothesis or conclusion. I = top is excluded. The zero ring is excluded
  by the existing local-ring class. A chain of length 0 gives the bound 0 ≤ degree.
- No universe bound is added: R has arbitrary universe u, and quotients and their
  prime spectra live in its natural universe. There is no independent test universe.

Searches actually run:

- `msearch.py`, leanfinder: “Krull dimension bounded by degree of eventual colength
  polynomials for all quotients using a shifted principal difference inequality”.
  Eight hits: `Ring.KrullDimLE`, `Polynomial.ringKrullDim_le`,
  `Ring.krullDimLE_iff`, `ringKrullDim_quotient_le`, polynomial/power-series dimension
  bounds, and quotient-plus-generator dimension bounds. None states this conditional
  theorem or defines this quotient colength function.
- `msearch.py`, loogle: `"ringKrullDim", "Polynomial"`. Nine hits concern dimensions
  of polynomial and multivariable polynomial rings; none matches the statement.
- `msearch.py`, grep, RingTheory: `colength.*(polynomial|degree)|prime.*chain.*(polynomial|degree)|hilbert.?samuel`.
  Zero hits in Mathlib.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, for colength, Hilbert--Samuel,
  prime-chain/polynomial keywords and the exact blueprint id. The relevant existing
  module is `Sheaf.RingTheory.HilbertSamuelGrowthDimension`, whose full statement was
  read: it asserts existence of a single polynomial with degree equal to dimension,
  not this conditional all-quotients monotonicity/drop/chain theorem. Its internal
  proof plan is not a public declaration of our statement. The scheme Hilbert--Samuel
  function has different arguments and exponent n+1, so cannot replace H_I(n).
- `rg` for `quotientPowerColength` and `primeChain_bound_of_colength_polynomials` in
  Mathlib, both project roots, and `dag/lean_names_upstream.json`: no collisions.

Validation: the first server compile diagnosed the namespace of `LTSeries`; the
Mathlib declaration is global, so `Order.LTSeries` was corrected to `LTSeries`.
The final module compiled separately as sandbox and library through `scompile.py`
with no errors or non-sorry warnings (4.2 s and 3.5 s respectively).

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
