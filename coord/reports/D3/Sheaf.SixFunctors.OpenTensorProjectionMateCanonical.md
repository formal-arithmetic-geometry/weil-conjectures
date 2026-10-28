## What changed

Added a proved private helper `canonicalProjectionMate_homEquiv` to
`Sheaf.SixFunctors.OpenTensorProjectionMateCanonical`.  It unfolds the canonical
mate and records its defining adjunction-transpose equation by
`Equiv.apply_symm_apply`.  The existing resolving-pair theorem remains marked
`STATEMENT-DISPUTED` and retains its single proof hole because its hypotheses do
not determine the supplied comparison families.

## Proved and sorry left

The helper `canonicalProjectionMate_homEquiv` is proved.  No existing hole was
closed.  The one existing `sorry` remains in
`WeilConjectures.CoefSupportOpenTensor.openTensorProjection_mate_canonical`,
node `lem-sf-open-tensor-projection-mate-canonical`.  No new `sorry` was added.

## No longer needed

None.  Both public imports remain required by the item's declarations and data.
No DAG nodes or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

`openTensorProjection_mate_canonical` is false as written.  Its
`ambientModel` and `openModel` arguments are arbitrary one-flat comparison
families, with no naturality or agreement with the simultaneous models.  A
single component can be postcomposed with a nontrivial automorphism while all
listed hypotheses remain unchanged, changing the right side of the displayed
equality.  The missing both-model and naturality hypotheses occur in the
resolving/descent statements.  A complete repair requires changing the
statement and its callers to carry those coherence data (or replacing the
families by the canonical normalized model).  The newly proved helper isolates
the part that is valid without those additional hypotheses.

## New nodes

None.  The helper is private and therefore has no public DAG node.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenTensorProjectionMateCanonical": "201d6e4247b0c3278a23fdec4e0ec07a3c7fc5a8"}, "results": {"Sheaf.SixFunctors.OpenTensorProjectionMateResolving": {"hash": "f5ea0fe848072fc4138e035b6a73d1af66e4609b", "status": "OK"}}, "seconds": 35, "time": "2026-10-28T07:46:41+0800", "transitive": 0, "version": 1}
```

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
