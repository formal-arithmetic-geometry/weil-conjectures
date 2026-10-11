## Worker report

The module `lean/Sheaf/RingTheory/ZariskisMainAway.lean` states
`Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime`. It uses Mathlib's
`integralClosure R S` for the integral closure and `Localization.awayMap` for the
map between principal localizations. The source hypotheses are rendered as follows:

- `R` and `S` are explicit types with `[CommRing R]` and `[CommRing S]`.
- The ring map is `[Algebra R S]` and finite type is `[Algebra.FiniteType R S]`.
- `q` is a prime ideal via `(q : Ideal S) [q.IsPrime]`.
- Quasi-finiteness at `q` is the dependency declaration
  `Algebra.IsQuasiFiniteAtPrime R S ⟨q, inferInstance⟩`.
- The conclusion is `∃ h : integralClosure R S, h.1 ∉ q ∧ ...`; the final clause is
  `Function.Bijective (Localization.awayMap (integralClosure R S).val.toRingHom h)`.
  This is the canonical Mathlib map sending the fraction represented by `y / h^n`
  to the corresponding fraction in `S`, exactly the node's localization map.

Dependency declarations used:

- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`.
- `Sheaf.RingTheory.QuasiFiniteAtPrime`: `Algebra.IsQuasiFiniteAtPrime`.
- `Mathlib.RingTheory.MonadLocalization.Away` / `Localization.Away` and
  `Localization.awayMap` (through `Mathlib.RingTheory.ZariskisMainTheorem`).
- `Algebra.FiniteType` from `Mathlib.RingTheory.FiniteType`.

Edge cases checked: `q` is explicitly prime; `h` is required outside `q`; the
localization permits `h = 1` (the identity localization), and no nonzero or domain
hypothesis is introduced. Universes `u` and `v` are explicit.

Searches made: `msearch.py leanfinder` for “Zariski main theorem finite type
quasi-finite prime integral closure localization away” returned Mathlib's
`Algebra.ZariskisMainProperty` and `of_finiteType`; `msearch.py loogle` for
`Algebra.ZariskisMainProperty.of_finiteType, Localization.awayMap` returned no
hit; `msearch.py grep` for `ZariskisMainProperty.of_finiteType` found the Mathlib
source theorem; `rg` over the project found no existing project declaration of
this target. The Mathlib theorem is not used as the statement because the node's
quasi-finite hypothesis is the project's fibre-spectrum predicate
`IsQuasiFiniteAtPrime`, whose equivalence to Mathlib's `Algebra.QuasiFiniteAt` is
proved separately.

## Earlier second reading (a previous round; superseded)

The statement was checked clause by clause against Stacks Algebra Theorem Tag 00Q9. The finite-type algebra, prime ideal, fibre-spectrum quasi-finiteness, integral-closure element outside the prime, and principal-localization bijectivity are all present with no extra assumptions. `integralClosure` and `Localization.awayMap` render the stated notions directly.

## Second reading by K1

I read the node statement, its Stacks source (Algebra Theorem 00Q9), the dependency
nodes, and the Lean module clause by clause.

- The node's objects `A → B`, finite type, integral closure `B'`, and prime
  `q ⊂ B` render as `(R : Type u) (S : Type v) [CommRing R] [CommRing S]
  [Algebra R S] [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime]`.
  The explicit universes preserve all ring cases.
- The node's quasi-finiteness-at-`q` hypothesis renders as
  `hq : IsQuasiFiniteAtPrime R S ⟨q, inferInstance⟩`, using the dependency's
  fibre-spectrum isolated-point definition. It introduces no stronger
  localization, domain, Noetherian, or characteristic assumption.
- The conclusion's element `h ∈ B'` and `h ∉ q` render as
  `∃ h : integralClosure R S, h.1 ∉ q`; `h.1` is the underlying element of
  Mathlib's integral-closure subring. The node's map `B'_h → B_h`,
  `y/h^n ↦ y/h^n`, renders exactly as
  `Function.Bijective (Localization.awayMap (integralClosure R S).val.toRingHom h)`.
  The existential and conjunction order agree exactly.

Edge cases are covered: `h = 1` is allowed (the `n = 0` source case), zero
rings and empty spectra are not excluded by the commutative-ring assumptions,
and no positive generator count, nonzero element, domain, or characteristic is
assumed. The independent universe parameters do not remove any source case.

I searched Mathlib and the project with LeanSearch/LeanFinder/Loogle and `rg`:
`Algebra.ZariskisMainProperty` and `of_finiteType` are the Mathlib theorem and
property, while no project declaration states this target. Mathlib's
`Algebra.QuasiFiniteAt` is a different localization-based predicate; the
project dependency `Algebra.IsQuasiFiniteAtPrime` is therefore used as recorded.
`integralClosure` and `Localization.awayMap` are the canonical Mathlib notions.

The worker statement was semantically faithful and compiled unchanged. I found
no hypothesis, object, quantifier, or conclusion mismatch. I expanded the theorem
docstring to carry the node proof's induction, conductor, localization, and
finite-subalgebra steps explicitly, satisfying the statement-documentation rule.
