## What changed

Restored `Sheaf.Paper.WeilIndProperOpenHigher` from quarantine and added the proof-only import
`Sheaf.Paper.WeilIndProperOpenHigherComparison`. The assigned theorem now obtains the
canonical comparison morphism and its `IsIso` witness and packages it as the requested
`Nonempty` isomorphism. Added the split-off comparison statement and its DAG node.

## Proved and sorry left

The target declaration `zlIndWeilProperOpenHigher` is proved from the comparison theorem.
One sorry remains in the new declaration `zlIndWeilProperOpenHigher_comparison`, recorded in
`lem-zl-ind-proper-open-higher-comparison-q7`.

## No longer needed

No imports were removed. The direct geometric and derived proof dependencies listed in the
original node are subsumed by the new comparison node; the target module itself uses only that
node in its proof.

## Where the brief, the DAG or earlier work was wrong

The quarantined source imported `Sheaf.Paper.WeilIndSheafCategory`, which is present in the
shared snapshot and compiles. The recorded global build failure was therefore a stale published
attachment (`bad import`) rather than an error in this module's source.

## New nodes

`lem-zl-ind-proper-open-higher-comparison-q7` states the canonical proper/open comparison
morphism with an `IsIso` witness. Its source is SGA 4, exposé XVII, 5.1.5--5.1.6 and
Bhatt--Scholze 6.7--6.8. It is stated in
`lean/Sheaf/Paper/WeilIndProperOpenHigherComparison.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.WeilIndProperOpenHigher": "56d0bbfabfc248e12e1604e1915ea66938ea425a", "Sheaf.Paper.WeilIndProperOpenHigherComparison": "e8cf0dbf4681647f9cf442bda43ec07a54aee320"}, "results": {}, "time": "2026-10-28T00:56:14+0800", "transitive": 0, "version": 1}
```

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
