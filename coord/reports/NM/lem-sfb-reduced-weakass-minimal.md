## Worker report

The module `Sheaf.RingTheory.WeakAssEqMinimalPrimes` states
`Ideal.weakAss_eq_minimalPrimes`, with `sorry` as its entire proof. It introduces
no definitions. The item's only changed field is `lean`.

Source checked: `literature/stacks-project/algebra.tex`, label
`lemma-reduced-weakly-ass-minimal`, Tag 0EMA, including its proof, and the local
criterion immediately preceding it. The source asserts the equality for every
reduced ring. There is no statement fault or correction.

Hypothesis and clause correspondence:

- “Let R be a commutative ring”: `(R : Type u) [CommRing R]`, with `universe u`
  explicitly declared. No universe or size restriction is imposed.
- “which is reduced”, with the stated positive-power criterion: `[IsReduced R]`.
  Mathlib's `IsReduced.eq_zero` says every nilpotent is zero. In a ring this
  is equivalent to the node's condition: a positive power killing x makes it
  nilpotent; a nilpotence witness of exponent zero forces `1 = 0`, hence `x = 0`.
- “Ann_R(x) = {a : ax = 0}”: the recorded dependency `Ideal.WeakAss` uses
  `((⊥ : Submodule R R).colon {x})`. Membership is `a • x = 0`, which is
  `a * x = 0` for the canonical self-module structure of R.
- “WeakAss(R)”, primes minimal over one such annihilator: `WeakAss R` in
  namespace `Ideal`, exactly the dependency definition, not a replacement.
- “exactly the set of minimal prime ideals”: the equality
  `WeakAss R = minimalPrimes R`. Mathlib's `minimalPrimes R` is the set
  of primes minimal over the bottom ideal, equivalently minimal among all primes
  (`minimalPrimes_eq_minimals`). Set equality supplies both inclusions.
- “No Noetherianity or finiteness assumption”: there are no such binders.
- “for the zero ring both sets are empty”: no `Nontrivial R` binder is present;
  both definitions require a prime ideal, which must be proper, and the zero ring
  has none. This is the zero-ring specialization of the same equality, not an
  extra assumption or an omitted case.

Dependency declarations read and used:

- Statement dependency `def-sc-weakly-associated-primes`:
  `Sheaf.RingTheory.WeaklyAssociated`, `Ideal.WeakAss`; its full body and
  docstring were read. Its module is publicly imported.
- Mathlib `minimalPrimes`, `IsMinimalPrime`, `Ideal.IsMinimalPrime`, and
  `Ideal.minimalPrimes` from `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`
  (publicly available through the statement dependency).
- Mathlib `IsReduced` from `Mathlib.Algebra.GroupWithZero.Basic`; its actual
  nilpotence-based definition and the subsingleton instance were read.
- Proof dependency `lem-sc-weakass-localization`:
  `Sheaf.RingTheory.WeakAssLocalization`, `Module.weakly_associated_atPrime_iff`;
  its full three-condition equivalence and proof docstring were read. Imported
  with plain `import` for the future proof.
- Proof dependency `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`.
- Proof dependency `def-weil-pbc-module-localization`:
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule`.
- Proof dependency `lem-weil-pbc-primes-of-localization`:
  `IsLocalization.AtPrime.orderIsoOfPrime` from
  `Mathlib.RingTheory.Localization.AtPrime.Basic` and
  `IsLocalization.orderIsoOfPrime` from `Mathlib.RingTheory.Localization.Ideal`.
  The two order-isomorphism signatures were read. These proof modules use plain
  imports. No dependency interface needs repair.

The theorem docstring carries every step of the node's proof: reduced nonzero
prime localization; the module localization criterion; the unit/nonunit split
forcing the localized maximal ideal to vanish; the prime correspondence; and
`Ann(1) = 0` for the reverse inclusion, including the zero-ring explanation.

Edge cases checked before writing: the zero ring is permitted and gives two
empty sets; a field gives the single prime zero, witnessed by 1; a domain has
minimal prime zero, and nonzero elements have zero annihilator. Products of
fields permit multiple minimal primes, so no domain hypothesis is used.
Arbitrary reduced rings with infinitely many minimal primes remain in scope.
The witness x = 0 has annihilator top and contributes no prime. The exponent
zero issue in Mathlib's nilpotence convention does not exclude the zero ring.

Searches (2026-10-24, `msearch.py`, group NM, this item):

- LeanFinder: “The weakly associated primes of a reduced commutative ring equal
  its minimal prime ideals”. Eight hits, including `minimalPrimes_eq_minimals`,
  `IsDomain.minimalPrimes_eq_singleton_bot`, radical/minimal-prime results and
  dimension-zero results; none asserts the requested equality.
- Loogle: `associatedPrimes, minimalPrimes`. Zero hits.
- Mathlib grep: `WeakAss|weaklyAssociated|weakly_associated|associatedPrimes.*minimalPrimes`
  in `RingTheory`. Zero hits.
- LeanSearch: “Weakly associated primes of a reduced commutative ring are exactly
  its minimal prime ideals”. Eight hits: minimal-prime definitions, associated
  primes, dimension-zero results, `PrimeSpectrum.isMin_iff`, and a prime-ideal
  singleton result; none states this theorem. The actual source of
  `AssociatedPrime/Basic.lean` was read: its radical-annihilator definition
  differs from arbitrary minimality over an annihilator. The relevant result
  in `AssociatedPrime/Localization.lean` assumes Noetherianity.
- `rg -n 'WeakAss|weakly_associated|weaklyAssociated'` separately over
  `lean/WeilConjectures` and `lean/Sheaf`: no upstream definition/theorem of
  this equality; project hits include the existing `Ideal.WeakAss`, its local
  criterion, zero-divisor and etale results, and geometric consumers.
- `grep -rn 'lem-sfb-reduced-weakass-minimal' lean/WeilConjectures`: no hits.
- `rg` for `weakAss_eq_minimalPrimes|weakAss.*[Rr]educed|[Rr]educed.*weakAss`
  in `dag/lean_names_upstream.json`, `lean/Sheaf`, and `lean/WeilConjectures`:
  no hits. The new declaration name is unused.

Validation uses the required `scompile.py` per-file server compile and
`deliver2.py --no-push` preflight. Only the expected sorry warning is acceptable.

## Second reading by NM

No second reading by another worker is claimed. This dispatcher assignment
requires direct worker delivery and prohibits spawning other agents; the
maintainer supplies the independent review. A final self-check compared the
node with the module: commutative ring and reducedness match the two instance
binders; weak association uses the recorded dependency; the conclusion is full
set equality with Mathlib's minimal primes; zero and non-Noetherian rings are
included. No mismatch or dependency repair was needed.
