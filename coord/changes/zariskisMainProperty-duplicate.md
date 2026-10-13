# zariskisMainProperty_of_isQuasiFiniteAtPrime

## Reason

The former Ideal-argument theorem was an unfolded duplicate of Mathlib's
`Algebra.ZariskisMainProperty.of_finiteType`. Its interface is replaced by a point-based
conversion theorem; callers are adapted to pass their existing `PrimeSpectrum` arguments to the replacement wrapper.
The semantic Zariski-main conclusion is unchanged because Mathlib's property unfolds to the
same integral-closure localization assertion.

## Old
```lean
theorem zariskisMainProperty_of_isQuasiFiniteAtPrime
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime]
    (hq : IsQuasiFiniteAtPrime R S ⟨q, inferInstance⟩) :
    ∃ h : integralClosure R S, h.1 ∉ q ∧
      Function.Bijective (Localization.awayMap (integralClosure R S).val.toRingHom h)
```

## New
```lean
theorem zariskisMainProperty_of_isQuasiFiniteAtPrime
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S)
    (hq : IsQuasiFiniteAtPrime R S q) : ZariskisMainProperty R q.asIdeal
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.QuasiFiniteLocalDimension | C1 | forced call through the point-based wrapper |
| Sheaf.RingTheory.QuasiFiniteAtFiniteSubalgebraAway | E1 | forced call through the point-based wrapper |
| Sheaf.Paper.IntegralClosureFiniteFibrePartLocalization | H1 | forced call through the point-based wrapper |

## Status
landed 20261013T211054-L-388715 2026-10-13 (merge of deliver/C1/Sheaf.RingTheory.ZariskisMainAway)
