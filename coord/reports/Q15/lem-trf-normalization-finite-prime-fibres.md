## Worker report

The module defines the theorem `RingTheory.normalization_finite_prime_fibres` in
`Sheaf.TraceFormula.NormalizationFinitePrimeFibres`. It states the finite-prime-fibre
result for the normalization `integralClosure R (FractionRing R)` of a commutative
Noetherian domain. For a prime `p : Ideal R`, the fibre is rendered as the subtype set
of prime ideals `Q` of the normalization whose contraction along
`algebraMap R (integralClosure R (FractionRing R))` equals `p`. The first conjunct
`Set.Finite ...` renders finiteness. The second conjunct says its `Set.ncard` is at
most the `Set.ncard` of `minimalPrimes` of the adic completion of the localization
`Localization.AtPrime p` at its maximal ideal. The binders `[CommRing R]`,
`[IsNoetherianRing R]`, `[IsDomain R]`, and `[p.IsPrime]` render respectively the
commutative-ring, Noetherian, integral-domain, and prime-ideal hypotheses. The proof is
`sorry` as required at stage 2.

The statement dependencies use Mathlib declarations recorded by the DAG:
`IsNoetherianRing` from `Mathlib.RingTheory.Noetherian.Defs`, `integralClosure` from
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, `Localization.AtPrime` from
`Mathlib.RingTheory.Localization.AtPrime.Basic`, and `IsAdicComplete`/the adic
completion API from `Mathlib.RingTheory.AdicCompletion.Basic` (with its ring structure
from `Mathlib.RingTheory.AdicCompletion.Algebra`). The proof-facing imports use
`Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`,
`Sheaf.RingTheory.IntegralComponentHenselianPermanence`, and
`Sheaf.RingTheory.NormalizationCompletedBranchLift`, whose declarations are recorded
in the proof dependency records.

Edge cases checked before writing include `p = ⊥` in a domain (the generic-fibre case),
where the completion of the localization is the fraction field and has one minimal
prime; the zero-dimensional field case; and the fact that `Set.ncard` is paired with an
explicit `Set.Finite` conjunct, so an infinite fibre cannot satisfy the statement merely
because `Set.ncard` returns zero on infinite sets. The formulation allows arbitrary
universe `u` and does not impose finite normalization or a finite-type hypothesis.

Searches performed: `msearch.py` leanfinder/loogle/grep for finite primes over a prime
and normalization fibres, plus `rg` over `WeilConjectures/` and the project `lean/Sheaf`.
Mathlib hits (`primesOver_finite`, `Algebra.QuasiFinite.finite_primesOver`, and related
finite-prime declarations) require Dedekind or quasi-finite hypotheses and do not state
the completed-branch bound; no exact existing declaration was found. No project or
upstream declaration named this theorem was found.

## Second reading by Q15

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
