## What changed

Proved the localization descent theorem by choosing a flat-term K-flat resolution of each
complex and applying a representative-isomorphism transport lemma. Added the strictly
smaller transport lemma as a separate module.

## Proved and sorry left

The target theorem `section_pull_normalized_localization_descent` is proved. One sorry
remains in `section_pull_normalized_localization_transport_iso`, the split-off transport
lemma.

## No longer needed

No imports or declared dependencies were pruned. The proof uses the flat-term K-flat
resolution infrastructure and the new representative transport lemma.

## Where the brief, the DAG or earlier work was wrong

The original one-step localization proof plan omitted the explicit representative
isomorphism transport statement needed to reduce an arbitrary complex to a flat-term
K-flat resolution. This delivery records that missing substep as a strictly smaller node.

## New nodes

`new-sfb-quotient-section-pull-transport-localization-iso`: representative-isomorphism
transport for the normalized localization equation.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.QuotientSectionPullTransportLocalization": "a2ba23e041f9831177d32847f5a24db9e1ffd003", "Sheaf.Paper.QuotientSectionPullTransportLocalizationIso": "08dc2395c2a9d1aecaadcc8825f8b89c86df183f"}, "results": {"Sheaf.Paper.QuotientSectionPullTransportExtension": {"hash": "3e53cea4a261930ca9e16d8af3e71d959cb32f83", "status": "OK"}}, "seconds": 72, "time": "2026-10-28T08:19:11+0800", "transitive": 0, "version": 1}
```

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
