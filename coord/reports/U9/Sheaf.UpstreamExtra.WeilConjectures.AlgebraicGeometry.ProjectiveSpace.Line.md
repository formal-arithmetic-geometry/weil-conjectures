## What changed

Restored the current quarantined source of
`Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line`, as recorded
in `coord/rework.tsv`, and reapplied the compilation repair. The live path is absent.
The public instance `AlgebraicGeometry.ProjectiveLine.Line_isIso` keeps its exact name,
universe, scheme parameter, proposition and instance registration. Its proof uses the
identical upstream isomorphism instance via `infer_instance`, rather than referring to
the upstream private helper `subsingleton_ne_zero`.

Removed ten dangling `variable (S) in` commands and the now-empty Frobenius section.
Wrapped the generated provenance comment to 100 columns. Removed three redundant
public imports already re-exported by the retained canonical Line import. No
source-library file or declaration changes. The change record is
`coord/changes/U9-projective-line-extracted-instance.md`.

On this repair attempt, copied the current quarantine file into the sandbox afresh and
compiled it through `lcompile.py`: it failed in 2.1 seconds with the unknown private
identifier, redundant binder annotation errors and unbalanced scopes. Reapplied the
repair to that fresh copy and compiled again: exit 0 in 2.0 seconds, no warnings.
This before/after check establishes a compilation repair against the current source.
The delivery tool fetches the current delivery base again before creating its commit.

## Proved and sorry left

Repaired `AlgebraicGeometry.ProjectiveLine.Line_isIso` using the already proved upstream
instance. The current quarantined item has zero `sorry`; the repaired item has zero
`sorry`. Holes closed: none. Holes added: none. Split off: none. No decomposition or
net proof-hole reduction is claimed.

## No longer needed

Removed explicit public imports, all still re-exported by
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line`:

- `WeilConjectures.AlgebraicGeometry.Frobenius`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearProjection`.
- `WeilConjectures.Mathlib.FieldTheory.Finite.Polynomial`.

The copied coordinate calculation and access to the upstream private subsingleton
helper are unnecessary because the upstream module proves the exact instance.
No whole modules or DAG nodes are pruned, and no declarations are withdrawn.

## Where the brief, the DAG or earlier work was wrong

Repaired the return at delivery head `91017ab2b0`, whose base `e0d550965` predated another
write to the item. Re-read the current return, U9 claim and rework row. The live source
is currently absent, and its preserved source remains at
`quarantine/Sheaf/UpstreamExtra/WeilConjectures/AlgebraicGeometry/ProjectiveSpace/Line.lean`.
Compared that source with the retained delivery, then restored it afresh and verified
its actual errors before reapplying the fix and compiling. The quarantine archive is
preserved; no deletion or empty replacement is requested. The new report and change
record address this return, superseding their stale references to head `460dcaef70`.

This is zero-hole quarantine rework, not an ordinary sorry-bearing item. The extraction
left a proof referring to a private name in another module and dangling binder commands
around an empty section. The upstream instance at
`WeilConjectures/AlgebraicGeometry/ProjectiveSpace/Line.lean:94` proves exactly the required
proposition over arbitrary schemes, with the same universes. Reusing it preserves the
statement, including the empty scheme case.

Current searches of `lean/`, `quarantine/`, `dag/nodes/` and `dag/units/` find no importer
of this extracted module, no external use of `Line_isIso`, and no node attaching this
module. No consumer adaptation is needed. The existing `sk-d-lines` node and unit still
use the unchanged upstream line geometry; their route and attachments are preserved.
The retained search log records LeanFinder, Loogle and msearch grep searches, and the
current upstream source confirms the exact match. No new node is needed.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
