## What changed

Added `Sheaf.CategoryTheory.IsoWhiskerCancellation`, which proves the generic
source-and-target isomorphism cancellation used by the intended cofinal-support
calculation. The item imports it and checks the composite support normalization
field before the unresolved composition equality.

## Proved and sorry left

Proved `CategoryTheory.cancel_iso_whiskers` in the new module. The assigned
`AlgebraicGeometry.Etale.SystemProjection.etaleCofinalSupport_composition` theorem
still has one sorry; no new sorry was added.

## No longer needed

None. The existing proof-dependency imports remain because the unresolved theorem
still has the stated route.

## Where the brief, the DAG or earlier work was wrong

The declaration is underdetermined as written. `CofinalSupport` contains independent
`compositionX`, `compositionY`, `factorX`, `factorY`, and `h` fields. Its `normalization`
field constrains each individual `h`, but imposes no relation between the fields for
`r`, `s`, and `s.trans r`. The assumptions `hi` and `hq` constrain only the projection
maps. Therefore the displayed subsequence cocycle cannot be derived for an arbitrary
`CofinalSupport`; a coherence field or an equivalent hypothesis is required. This is
already recorded by the `STATEMENT-DISPUTED` comment in the module.

## New nodes

`lem-pur-etale-cofinal-support-iso-cancellation` records the proved generic
cancellation lemma and its module.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.CategoryTheory.IsoWhiskerCancellation": "032efc923e1e019e3a2179fd886798b26916fe62", "Sheaf.Paper.EtaleCofinalSupportComposition": "8894a1963846e75ab429e47955b2a06a37615fbf"}, "results": {"Sheaf.Paper.EtaleSystemCofinalMate": {"hash": "35ffc1a3876fb6fd8c6408d2029405d2abe2c6d1", "status": "OK"}}, "seconds": 29, "time": "2026-10-28T03:41:09+0800", "transitive": 0, "version": 1}
```

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
