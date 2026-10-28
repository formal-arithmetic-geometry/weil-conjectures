## What changed

Repaired the disputed statement of
`WeilConjectures.CoefSupportOpenTensor.openTensorProjection_mate_canonical`.
Added `ambientBoth`, `openBoth`, `hC` and `flatC`: the one-flat comparison
families must agree with the simultaneous models, and C is a flat-term K-flat
representative. These are exactly the four assumptions already present in
`openTensorProjection_mate_resolving` which its former proof discarded.
Adapted that caller to pass them, preserving its entire public signature,
visibility and imports. Updated the item's DAG statement, Lean attachment,
proof plan and statement-change record. Expanded the theorem docstring into a
complete proof in words of the corrected resolving-pair claim.

This supersedes the earlier diagnostic-only G2 packet at 67567487100; the
substantive change here is the normalization/resolving-pair statement repair.
That diagnostic packet's wording about both sides was inaccurate: the left side
does depend on openModel. The valid counterexample changes ambientModel alone.

Change record:
`coord/changes/G2-open-tensor-projection-canonical-normalization.md`.

## Proved and sorry left

Holes closed: none. Holes added: none. The one existing named theorem hole
remains in
`WeilConjectures.CoefSupportOpenTensor.openTensorProjection_mate_canonical`
(node `lem-sf-open-tensor-projection-mate-canonical`), now with the corrected
statement and its full intended argument in the docstring. This is a statement
repair, not a proof of the former false claim and not a decomposition. The
caller `openTensorProjection_mate_resolving` retains a complete proof from the
corrected statement. The pre-existing private helper
`canonicalProjectionMate_homEquiv` is unchanged and proved.

## No longer needed

No imports, DAG nodes or modules are pruned. The private canonical-mate helper
and definition remain unchanged. The four dummy `have _ := ...` lines in the
resolving caller are removed because those assumptions are now actually passed
to the canonical theorem.

## Where the brief, the DAG or earlier work was wrong

The earlier split strengthened the parent's resolving-pair statement incorrectly:
it dropped agreement of the one-flat comparisons with T and T′ and dropped the
resolving assumptions on C. Since `RingedDerivedTensorComparison` is merely a
family of isomorphisms, changing the ambient component by a nontrivial
automorphism changes the right side while fixing every datum on the left.
The new statement restores the hypotheses of the existing caller, matching the
canonical tensor models in Stacks 0GL1 and 06YS--06YT. It does not change any
target statement or any definition used by a target.

The sole DAG citer is `lem-sf-open-tensor-projection-mate-resolving`. Its use
still holds because it already has all four added hypotheses. The unit's route
is unchanged. The server's current records were checked: the item is claimed
by G2, the resolving caller is unclaimed, there is no rework row and no current
build-error record. The metadata's `statement_change.by` uses the legacy
`G2 stage 2` spelling required by its schema; this is a stage-3 repair.

The corrected item and adapted caller compile in import order (8.5 s and 9.9 s).
The caller's original version fails against the changed dependency at its sole
application: `openModel` is supplied where `ambientBoth` is now expected (line
125). This confirms that passing the added arguments is a necessary adaptation.
The unchanged descent importer compiles against the adapted caller (39.4 s); its
temporary sandbox source copy was removed, so it is not part of the delivery.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenTensorProjectionMateCanonical": "0961f84023b9d7f12c24074056f5efc6404a59df", "Sheaf.SixFunctors.OpenTensorProjectionMateResolving": "96831495c8feae0ca52458de34567e05caee1771"}, "results": {}, "time": "2026-10-28T10:15:41+0800", "transitive": 0, "version": 1}
```

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
