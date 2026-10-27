## What changed

The target theorem now applies `exists_affine_projectiveBundle_presentations` to obtain an affine
open cover and combines the resulting local properness statements with
`IsZariskiLocalAtTarget.of_iSup_eq_top`.  The unresolved affine comparison is isolated in the
new module `Sheaf.TraceFormula.CanonicalRelativeProjProperLocal`.

## Proved and sorry left

Closed `canonicalRelativeProj_proper` (one target sorry).  Added one strictly smaller split
statement, `canonicalRelativeProj_restrict_proper`, whose proof remains `sorry` and whose
proof plan is recorded in its docstring and DAG node.

## No longer needed

The parent proof no longer directly needs `lem-trf-projective-bundle-quotient-geometry` or the
separate `lemma-nagata-projective-target-local` node: the local comparison is isolated in the
split lemma, and target-locality is supplied directly by Mathlib.  The parent also no longer
uses the old direct proof route through those declarations.

## Where the brief, the DAG or earlier work was wrong

The original parent proof dependencies treated the affine restriction as if its relative Proj
were definitionally the corresponding global chart.  The restriction module and the global
chart use distinct sheaf models, so an explicit normalized symmetric-algebra pullback and
arrow-isomorphism comparison is required.  The target statement itself is unchanged.

## New nodes

`lem-trf-canonical-relative-proj-proper-local` in
`dag/nodes/sec-trace-formula/lem-trf-canonical-relative-proj-proper-local.json`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.TraceFormula.CanonicalRelativeProjProper": "9f0bee42fa043dad663c2ea4f2c62b730e4ce55b", "Sheaf.TraceFormula.CanonicalRelativeProjProperLocal": "7fd87184b760978adad890eb8a90576d1b31cd4a"}, "results": {}, "time": "2026-10-28T05:25:06+0800", "transitive": 0, "version": 1}
```

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
