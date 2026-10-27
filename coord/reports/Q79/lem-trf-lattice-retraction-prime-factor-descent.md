## Worker report

The module `Sheaf.RingTheory.LatticeRetractionPrimeFactorDescent` states
`RingTheory.latticeRetraction_prime_factor_descent`, with one postponed proof (`sorry`).
No definitions, auxiliary theorems, new nodes or dependency repairs are needed. The
accepted stage-1 split, statement, statement dependencies and proof dependencies are
unchanged. The previous worker's stage-1 live-wins refusal does not apply: the current
node has no Lean binding and coord/brief-stage2.md section 0 explicitly authorizes this
stage handoff. No released repair note names this item.

Hypotheses, matched individually:

- A commutative domain D: `{D : Type u} [CommRing D] [IsDomain D]`, with explicit universe.
- A unital subring R of D: `(R : Subring D)`. Its canonical subtype scalar action on D
  is Mathlib's action, used by `D →ₗ[R] R`; it is multiplication by the included scalar.
  The same subset is closed under that action, exactly the stated R-submodule notion.
- An integer r >= 0 and the r elements: `(r : ℕ) (x : Fin r → D)`.
- Each element is a nonzero prime nonunit: `(hx : ∀ i : Fin r, Prime (x i))`.
  Mathlib's `Prime` is exactly nonzero, nonunit and prime divisibility, not irreducibility.
- For every natural vector a, the monomial is `∏ i : Fin r, x i ^ a i`.
- A subgroup of the integral lattice: `(M : AddSubgroup (Fin r → ℤ))`.
  Membership of a natural vector in that lattice means `(fun i ↦ (a i : ℤ)) ∈ M`.
- All nonnegative lattice monomials belong to R: `hmon`, quantified over every natural
  vector and then its lattice-membership proof. No basis, saturation or rank is assumed.
- An R-linear retraction: `(ρ : D →ₗ[R] R)` and `hρ : ∀ z : R, ρ (z : D) = z`.
  No multiplicativity or ring-hom condition is imposed on the retraction.
- Vanishing outside the lattice: `hsupport`, for every natural vector not in M.
- Unit preservation: `hunits : ∀ v : Dˣ, IsUnit (ρ (v : D))`. Each unit element is the
  value of a bundled unit, so this is precisely the node's condition on all units.
- A positive natural lattice vector: `w : Fin r → ℕ`, `hw` for lattice membership,
  and `hwpos : ∀ i : Fin r, 0 < w i`. An arbitrary supplied witness renders the stated
  existence assumption without restricting which witness can be used.
- Every natural lattice vector s: `s : Fin r → ℕ` and `hs` for its membership.
- Factors h,h' in R: `(h h' : R)` with `hh` their product equal to x^s after inclusion in D.
  Inclusion is injective, so this is the same factorization as an equality in R.

Conclusions, matched individually:

- `∃ (e : Fin r → ℕ) (he : (fun i ↦ (e i : ℤ)) ∈ M)` gives a nonnegative lattice vector.
- `e ≤ s` is pointwise order, hence precisely coordinatewise comparison.
- `v : Dˣ` and `(h : D) = (∏ i : Fin r, x i ^ e i) * (v : D)` give the ambient unit
  and factorization in D.
- `u : Rˣ` and `(u : R) = ρ (v : D)` give the subring unit and its specified value.
- `h = (⟨∏ i : Fin r, x i ^ e i, hmon e he⟩ : R) * (u : R)` is the equality in R,
  with exactly the monomial already known to belong to R. The subtype is a concrete
  construction using the supplied membership proof, with no choice or postponed data.

Dependencies read and used:

- `def-weil-submodule-span` is a Mathlib leaf, recorded as `Submodule.span` in
  `Mathlib.LinearAlgebra.Span.Defs`. Its full signature and docstring define the least
  submodule containing a set; `Submodule` in `Mathlib.Algebra.Module.Submodule.Defs`
  supplies the scalar-closed additive subgroup notion. The recorded module is publicly
  imported. No private replacement of span or submodule is introduced.
- The proof dependency `lem-trf-prime-product-factor-splitting` is a Mathlib leaf whose
  match is `mul_eq_mul_prime_prod` in `Mathlib.RingTheory.Prime`. Its full signature and
  docstring were read: it partitions the indexed finite prime product and splits the
  coefficient, with no UFD hypothesis. Its module is imported for the future proof only.
- `Subring` from `Mathlib.Algebra.Ring.Subring.Defs`, `Algebra.ofSubsemiring` from
  `Mathlib.Algebra.Algebra.Basic`, `AddSubgroup` from
  `Mathlib.Algebra.Group.Subgroup.Defs`, and `Prime` from `Mathlib.Algebra.Prime.Defs`
  are the existing Mathlib notions; their definitions and relevant instance were read.

Edge cases checked against the proof plan: r=0 leaves an empty coordinate type; the
positivity hypothesis is vacuous, all monomials equal one, and e=0. When s=0, hh'=1,
so h is a unit in R and the conclusion takes e=0 and v=h included in D. Coordinates
of s may individually vanish. Repeated and associated x_i are allowed because the
prime-product theorem uses labelled copies rather than distinct prime values. M need
not be saturated or full rank. There is no factoriality, Noetherian, characteristic,
locality or nonempty-coordinate assumption. The zero ring D is excluded exactly by
the word domain. If M has no positive vector the explicit witness hypothesis cannot
be supplied, as in the node. No false or untypable statement was found.

Source read: ILO Expose VI, printed pages 69--70 (PDF pages 75--76), sections 1.4 and
1.6(i)--(ii), through pdftotext. These pages supply context only; the detailed auxiliary
proof is the agent argument in the node, reproduced in the theorem's docstring. The
current stage-1 Q82 report and review were also read; no current blueprint unit is
being replaced or altered.

Searches (all via the prescribed msearch.py wrapper, 2026-10-23):

- leanfinder: “Descent of prime monomial factors along a subring linear retraction which
  kills exponents outside an additive subgroup and preserves units”. Eight hits; PID
  factor/submonoid and polynomial presentation/localization results do not give the
  lattice-support retraction assertion and add hypotheses or different objects.
- loogle: `Prime, LinearMap, IsUnit`. Zero hits.
- leansearch: “A factor of a product of prime powers descends to a monomial with lattice
  exponent under a unit preserving subring linear retraction”. Eight hits, including
  `MvPolynomial.dvd_monomial_one_iff_exists` (a polynomial-only statement), UFD results
  (an extra hypothesis), and `comap_prime` (descent of primality, not factors or support).
  None matches this statement.
- Mathlib grep: `retraction.*prime|prime.*retraction|lattice.*monomial|monomial.*lattice`.
  Zero hits.
- Project rg in lean/WeilConjectures and lean/Sheaf:
  `lattice.*[Rr]etraction|[Rr]etraction.*[Pp]rime|lattice_retraction|latticeRetraction`.
  Only unrelated henselian/etale retraction matches. Searching the exact node id in
  both directories found no declaration. The full upstream-name list was also checked
  for the chosen declaration name before delivery.

Validation: scompile.py compiled both sandbox and library module modes without errors
or warnings. The first probe needed a public import of Mathlib.Algebra.Prime.Defs,
which is now present; the proof-only RingTheory.Prime import stays private.

## Second reading by Q79

This is the worker's explicit second pass over the node and finished module; the
maintainer supplies the independent review. No other agent was started, as the brief
prohibits that. I checked every binder and conjunction above against the unchanged
node. In particular, Prime includes both nonzero and nonunit clauses, hwpos is strict,
all natural vectors are cast coordinatewise to the integral lattice, and hunits ranges
over every unit in D. The conclusion keeps the ambient unit v and subring unit u
separate, requires u=ρ(v), and states the equality in R using hmon e he. Thus no
ambient equality silently replaces the final subring equality. No extra distinctness,
UFD or ring-map assumption appears. All variables and the single universe are bound.
The one visibility fault from the first compilation was fixed by the public Prime
import, without changing the statement. The module contains exactly one theorem and
its proof is sorry. No new nodes or statement correction are present.
