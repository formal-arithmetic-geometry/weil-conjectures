## What changed

Restored `lean/Sheaf/Paper/FiniteIntrinsicProjectionCompatibility.lean` from the
quarantine path required by the current rework assignment.  The declaration remains
unchanged and its disputed-status comment now records explicitly why the supplied
family of isomorphisms is insufficient for the displayed equation.

## Proved and sorry left

No holes were closed.  The single hole left is
`WeilConjectures.IntegralProjectionReduction.finiteIntrinsicProjectionCompatibility`
in the item's node `new-sf-finite-intrinsic-projection-compatibility`.  The theorem is
marked `STATEMENT-DISPUTED`: `e X` and `e Y` are independent components, while the
equation relates them through the morphism `f`; replacing `e Y` by an unrelated
automorphism changes the right-hand side without changing the source comparison.
No new holes were added.

## No longer needed

None.  The existing imports and proof-dependency declarations remain necessary for the
statement's types and for the intended future repair.

## Where the brief, the DAG or earlier work was wrong

The DAG and module statement omit the naturality (or normalization) condition on `e`
needed to compare its components along `f`.  The proof prose assumes precisely this
missing compatibility, so it cannot establish the statement as written.  A future
repair must change the statement under the project's statement-change procedure before
the hole can be proved.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteIntrinsicProjectionCompatibility": "2487ddc35a3c396d12ae08cf7c38d84c82c74d31"}, "results": {}, "time": "2026-10-28T06:24:22+0800", "transitive": 0, "version": 1}
```

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
