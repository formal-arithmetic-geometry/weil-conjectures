## What changed

The item module now constructs `ComparisonData` from four independent component witnesses. It
imports the four new component-existence modules and assembles their `.some` fields into the
record. The existing `ComparisonData` and target theorem statements are unchanged.

## Proved and sorry left

The target theorem `etaleSystemProjectionComparisonData_nonempty` is proved completely by
record assembly. Four strictly simpler component theorems are added with `sorry`, each naming
one missing construction step:

- `supportEvaluation_nonempty` (node `lem-pur-etale-system-projection-support-evaluation-existence`);
- `scalarEvaluationX_nonempty` (node `lem-pur-etale-system-projection-scalar-evaluation-x-existence`);
- `scalarEvaluationY_nonempty` (node `lem-pur-etale-system-projection-scalar-evaluation-y-existence`);
- `restrictionSupport_nonempty` (node `lem-pur-etale-system-projection-restriction-support-existence`).

## No longer needed

The target proof no longer uses the four generic proof dependencies recorded by the original
DAG step (`lem-coef-semilinear-derived-sections`,
`lem-pur-sheaf-ring-derived-coefficient-adjunction`,
`lem-pur-system-level-left-extension`, and
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`). Their imports were not present in
the item module; the corresponding dependency edges are pruned from the item node.

## Where the brief, the DAG or earlier work was wrong

The original proof step treated the normalized support, scalar, and restriction comparisons as
an immediate consequence of generic derived-category infrastructure. Those declarations do not
construct any of the required comparison records. The delivery therefore splits the step into
four component existence statements and proves the original target by a real constructor.

## New nodes

`lem-pur-etale-system-projection-support-evaluation-existence` records existence of one
normalized support evaluation comparison.

`lem-pur-etale-system-projection-scalar-evaluation-x-existence` records existence of one
normalized source scalar evaluation comparison.

`lem-pur-etale-system-projection-scalar-evaluation-y-existence` records existence of one
normalized target scalar evaluation comparison.

`lem-pur-etale-system-projection-restriction-support-existence` records existence of one
normalized compact-support restriction comparison.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.EtaleSystemProjectionComparisonData": "d4cc1e7d5bd3d631cec1d7fead33d82c3f36feff", "Sheaf.Paper.EtaleSystemProjectionRestrictionSupportExistence": "df9e0708c76ac0a70894b69b5d111e61845c9ec8", "Sheaf.Paper.EtaleSystemProjectionScalarEvaluationXExistence": "2a47443ad81cf7e763a0e0098ec7fa1fd8de5eaa", "Sheaf.Paper.EtaleSystemProjectionScalarEvaluationYExistence": "fa05087d5ad9c360d5ec842a08e6fc4d5454273b", "Sheaf.Paper.EtaleSystemProjectionSupportEvaluationExistence": "c96d33aa2b5962a33d36494033859586fd7a4733"}, "results": {}, "time": "2026-10-28T03:38:07+0800", "transitive": 0, "version": 1}
```

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
