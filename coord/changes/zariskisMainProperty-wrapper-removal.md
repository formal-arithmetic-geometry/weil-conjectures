# Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime

## Reason

Repair upstream review #1428: the old theorem repeats Mathlib's Zariski-main conclusion.
Keep only its independent conversion of the project's isolated fibre point hypothesis
into Mathlib's QuasiFiniteAt. Each caller applies Mathlib's of_finiteType directly.
This is an intermediate interface repair, not a proof of a formerly open hole.
No definition or target statement changes, and all caller signatures stay identical.

## Old

```lean
theorem zariskisMainProperty_of_isQuasiFiniteAtPrime
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S)
    (hq : IsQuasiFiniteAtPrime R S q) : ZariskisMainProperty R q.asIdeal
```

## New

```lean
theorem zariskisMainProperty_of_isQuasiFiniteAtPrime
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S)
    (hq : IsQuasiFiniteAtPrime R S q) : QuasiFiniteAt R q.asIdeal
```

Mathlib.RingTheory.ZariskisMainTheorem becomes a proof-only import. The public
QuasiFinite.Basic import supplies the new result type; every adapted caller adds a
plain ZariskiMainTheorem import to obtain its proof declarations explicitly.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.ZariskisMainAway | K2 | repaired result type; no hollow definitions |
| Sheaf.RingTheory.QuasiFiniteLocalDimension | C1 | conversion instance followed by Mathlib's theorem; unchanged signature |
| Sheaf.RingTheory.QuasiFiniteAtFiniteSubalgebraAway | E1 | conversion instance followed by Mathlib's theorem; unchanged signature |
| Sheaf.Paper.IntegralClosureFiniteFibrePartLocalization | H1 | conversion instance followed by Mathlib's theorem; unchanged signature |

The downstream.py --uses search found exactly these four textual uses, including
the declaration itself. All three original caller proofs fail against the repaired
interface; their changed lines only register the conversion instance, apply the
original Zariski-main theorem, and import that proof theorem explicitly. The other
transitive importers do not call the changed declaration. All four direct importers
import this module privately, so removing its public Zariski-main import does not
remove any public API of theirs. No target uses this theorem in its statement or
uses a changed definition; no target semantic review is reopened.

## Status

landed 20261013T215607-L-899022 2026-10-13 (merge of deliver/K2/Sheaf.RingTheory.ZariskisMainAway)
