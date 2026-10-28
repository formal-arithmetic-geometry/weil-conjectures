## What changed

Proved `WeilConjectures.IteratedPurityScalarPasting.family_existsUnique` in
`Sheaf.Paper.IteratedPurityScalarPasting`, using the existing rational comparison
identification theorem for existence. Added proved private helpers for uniqueness
of source localization, purity, scalar comparisons and shift structures. Four
private proof imports provide the existing comparison theorem, good-complex
localization, integral residue Tor identification, and residue-field coefficient
units. Existing public imports and all mathematical signatures are retained;
the existential binder is renamed `_V` solely to silence the unused-binder linter.
No other module is changed. Updated the item's node to record this proof while
retaining its remaining eight-step composition plan. The module compiled
with exit code zero in 40.1 seconds. The binder-only change is recorded in
`coord/changes/D4-iterated-purity-family-binder.md`.

## Proved and sorry left

Closed one of the original two holes:
`WeilConjectures.IteratedPurityScalarPasting.family_existsUnique`.
This is a proof from the existing stated comparison theorem, not an axiom-free
proof of that theorem's transitive dependencies.

One original hole remains:
`WeilConjectures.IteratedPurityScalarPasting.iteratedPurityScalarPasting`
(node `lem-pur-iterated-purity-scalar-pasting`). Its statement, complete source
proof docstring and body are unchanged. Added zero holes; split off zero holes.

## No longer needed

None. No import, declaration, module or DAG dependency was pruned. The original
composition dependencies remain necessary for the unfinished main theorem.

## Where the brief, the DAG or earlier work was wrong

The local queue snapshot omitted the live assignment; the current server queue
confirmed two proof holes and the D4 claim. The stored build-error file reports
old bad imports, not a new collision or definition repair. The cited
`lem-pur-rational-normalized-purity-diagrams` has no Lean attachment in the shared
snapshot, but the existing `rationalScalarComparisonIdentification` states the
single-morphism data needed for the family proof. Good-complex localization is
an existing proved private theorem, accessed by a private `import all`.

The main pasting theorem remains substantial. In particular the source shift
structures involve the supplied exceptional systems' localization shifts; these
must be reconciled with the specified compositor, not replaced by arbitrarily
chosen compatible shifts. No proposed split or extra hypothesis was retained.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IteratedPurityScalarPasting": "8afdfec8205ff06204182e9af7850f13cc65f261"}, "results": {}, "time": "2026-10-28T14:43:28+0800", "transitive": 0, "version": 1}
```

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
