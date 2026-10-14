# Algebra.zariskisMainProperty_of_isQuasiFiniteAtPrime

## Reason

Complete the wrapper removal requested by upstream review #1428. The earlier K2
repair removed the duplicate localization conclusion but retained a conversion-only
theorem under the same name. Remove that remaining wrapper, and have its three
callers use Mathlib directly, including the short transport of the fibre hypothesis.
No mathematical statement, definition, target signature or caller signature changes.

## Old

```lean
theorem zariskisMainProperty_of_isQuasiFiniteAtPrime
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S)
    (hq : IsQuasiFiniteAtPrime R S q) : QuasiFiniteAt R q.asIdeal
```

## New

The declaration is removed, with no replacement declaration. The module retains
both public imports so its existing public import interface is preserved.
Each caller supplies a local `QuasiFiniteAt` instance using
`QuasiFiniteAt.of_isOpen_singleton_fiber`, transports its hypothesis using
`PrimeSpectrum.preimageHomeomorphFiber`, `Homeomorph.isOpen_image` and
`Set.image_singleton`, and retains its existing application of
`Algebra.ZariskisMainProperty.of_finiteType`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.ZariskisMainAway | Y3 | removes the remaining wrapper |
| Sheaf.RingTheory.QuasiFiniteAtFiniteSubalgebraAway | unclaimed | local conversion; removes private wrapper import |
| Sheaf.RingTheory.QuasiFiniteLocalDimension | unclaimed | local conversion; removes private wrapper import |
| Sheaf.Paper.IntegralClosureFiniteFibrePartLocalization | unclaimed | local conversion; removes private wrapper import |

`tools/downstream.py --uses` finds only these three callers and the declaration.
Every caller signature and visibility is identical. Original callers fail with an
unknown identifier for the removed theorem; only the failing conversion line and
its obsolete proof import are changed. The delivery tool records the exact
counterfactual compiler errors in the report. All adapted files compile.
The fourth direct importer, Sheaf.RingTheory.QuasiFiniteIntegralClosureOpen, has
an unused private wrapper import and no use of the declaration. It remains
unchanged: it still compiles, so adapting it would not be forced.
No target statement mentions the removed theorem and no definition changes,
so target semantics do not require review.

## Status

landed 20261014T030650-L-345626 2026-10-14 (merge of deliver/Y3/Sheaf.RingTheory.ZariskisMainAway)
