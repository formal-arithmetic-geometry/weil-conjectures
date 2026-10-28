## What changed

Proved the ordinary associativity clause by evaluating the normalized direct-image comparison on sections and applying adjunction composition coherence. Split the left and right unit clauses into named statements for follow-up proof.

## Proved and sorry left

Closed `ordinary_coherence`, which proves the associativity conjunct. Left `ordinary_pullback_rightUnit` and `ordinary_pullback_leftUnit` as two named intermediate theorems with `sorry` proofs.

## No longer needed

No imports or DAG dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The original module bundled ordinary associativity and both unit laws. The associativity route is independently formalizable from `Adjunction.leftAdjointCompIso_assoc`; the unit calculations require the section-level identity comparisons and are split as strictly smaller conjunctive statements.

## New nodes

- `new-lem-sf-ambient-pullback-ordinary-right-unit`
- `new-lem-sf-ambient-pullback-ordinary-left-unit`

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AmbientPullbackOrdinaryCompositionLaws": "7bd434d5e6dde63a213d5434312b59f4a8eae47d"}, "results": {"Sheaf.Paper.AmbientPullbackCompositionLaws": {"hash": "7f16387c2823c52b71d11566fc319662f47ef068", "status": "OK"}}, "seconds": 12, "time": "2026-10-28T09:53:30+0800", "transitive": 0, "version": 1}
```

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
