## What changed

Repaired `Sheaf.Paper.WeilIndProperHigherRealization` by splitting off the proper-image existence/comparison step into `Sheaf.Paper.WeilIndProperHigherRealizationExists`. The parent proof transports the resulting carrier isomorphism from the chosen represented object to the supplied representative using full faithfulness of `zlWeilIndEmbedding`. Both sandbox modules compile with `lcompile.py --all`.

## Proved and sorry left

- Closed the original `sorry` in `zlIndWeilProperHigher_realization`.
- Added one strictly simpler intermediate theorem, `zlIndWeilProperHigher_realization_exists`, whose proof remains `sorry`; it is the existence/comparison input for a represented proper higher image.

## No longer needed

No imports were removed. The proof uses the geometric-fibre properties, compact-support coefficient action, constructible truncations, and the ind-sheaf category; all remain needed by the statement or proof.

## Where the brief, the DAG or earlier work was wrong

The current global build error identified the quarantined upstream import chain, but the live dependency modules compile. The original module had no usable decomposition for the realization comparison; the new node records the required existence/comparison step separately.

## New nodes

- `lem-zl-ind-proper-higher-realization-exists` — `Sheaf.Paper.WeilIndProperHigherRealizationExists.zlIndWeilProperHigher_realization_exists`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.WeilIndProperHigherRealization": "6aacb744ac1e9ece65efe7f9a05de9def5c83f59", "Sheaf.Paper.WeilIndProperHigherRealizationExists": "fcff33b4be3f6313f152eae97bca0175da2f5b1b"}, "results": {}, "time": "2026-10-28T01:14:15+0800", "transitive": 0, "version": 1}
```

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
