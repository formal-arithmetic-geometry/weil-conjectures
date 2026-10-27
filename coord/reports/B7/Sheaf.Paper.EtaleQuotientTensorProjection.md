## What changed

The item now applies the unbounded proper mate identity and the open-factor pasting theorem. Two new proof modules state the strictly smaller proper mate and open pasting steps; the item itself has no remaining `sorry`.

## Proved and sorry left

The item theorem `AlgebraicGeometry.Etale.etaleQuotientTensorProjection` is proved from the two intermediate declarations. The delivery adds two named intermediate theorems with `sorry`: `AlgebraicGeometry.Etale.scalarMate_restrict_eq_projection_unbounded` and `AlgebraicGeometry.Etale.etaleQuotientTensorProjection_of_proper_mate`. No `sorry` remains in the item module.

## No longer needed

The item proof no longer directly uses `Sheaf.Paper.EtaleQuotientTensorProjectionProperFactor`; that import is removed from the item. The proper-factor module remains imported by the open-pasting module, where it is available to the assembly proof.

## Where the brief, the DAG or earlier work was wrong

The prior item proof left the target unchanged after introducing `compactScalarMap_proper_open_factor`. The unbounded scalar mate calculation is a separate required step; it cannot use the existing bounded-below theorem without adding hypotheses. The delivery records this distinction as two strict intermediate statements.

## New nodes

`lem-pur-etale-quotient-tensor-projection-proper-mate` records the unbounded proper mate projection identity and is realized by `Sheaf.Paper.EtaleQuotientTensorProjectionProperMate`.

`lem-pur-etale-quotient-tensor-projection-open-pasting` records the open restriction and constant-tensor pasting conditional on that proper identity and is realized by `Sheaf.Paper.EtaleQuotientTensorProjectionOpenPasting`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.EtaleQuotientTensorProjection": "9bfb021beab62db64c7f612f59f8c862dfbe62bc", "Sheaf.Paper.EtaleQuotientTensorProjectionOpenPasting": "6dd812e3e96fc6a3e4dfe007c2010f627d6c7740", "Sheaf.Paper.EtaleQuotientTensorProjectionProperMate": "281e342b7e002e6307ed23c3b0173a7d12c557bb"}, "results": {"Sheaf.Paper.EtaleSystemQuotientNormalization": {"hash": "89bf0d55fdca40ad4e23fa5a7537f7660e0d0573", "status": "OK"}}, "seconds": 173, "time": "2026-10-28T03:42:56+0800", "transitive": 0, "version": 1}
```

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
