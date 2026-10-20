## What changed

Retired `Sheaf.Algebra.Homology.KFlatPullback` in favour of its official
`WeilConjectures` twin. Nine retained consumers switch their assigned import, preserving its visibility,
with every signature and proof body unchanged. Six pre-existing overlong instance
lines in global monoidal normalization are wrapped to satisfy preflight.
`IsKFlatTensor` in the twin is definitionally equal to `IsAcyclicTensorKFlat`.

Also retired the unclaimed consumer
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`: no remaining source
imports it, and its official twin supplies the same six public statements. Both
DAG attachments now point at the official twins. Both withdrawals appear in
`deleted.txt`. Change record:
`coord/changes/retire-kflat-pullback-20261020.md`.

Return repair (reviewer C-b44ac, returned head `b44ac794a90`): reread the
current shared module after landing `ba90540c48d`. That landing replaces its
Sheaf stalk-comparison import by the official twin and uses the canonical stalk
ring map and chain isomorphism. The official KFlatPullback twin already uses
that canonical construction, so retirement preserves this intervening repair.
Reconstructed all nine retained consumers from their current shared sources and
reapplied only the reviewed import replacements and six line wraps. This retains
a concurrent landing's switch to the official IsKFlatTilde import in
AffineKFlatPullbackChartComparison. The node copies change only their Lean
attachments. Both withdrawal paths still exist in the current source tree;
neither is a quarantined or already-absent file. The delivery tool rebuilds the
replacement packet against the fetched current sheaf-dag base. Recompiled
all nine retained consumers on this retry; AffineKFlatPullbackChartComparison
compiled in 27.3 seconds after retaining the concurrent import change.

The initial batch compiled all ten adapted consumers cleanly, each below 60 seconds
(10.4–49.5 seconds). The unused affine consumer later timed out during repeated
validation; experimental performance changes were discarded before its withdrawal.
The delivery tool compiled all nine retained consumers. Its first preflight
refused six pre-existing overlong lines in global monoidal normalization; these
are now wrapped without changing tokens. The corrected dry run passed compilation, axiom probes, and preflight
(commit `e356a754eed`, CODEX review class). An import
scan finds no remaining importer of either withdrawn module and no new environment
containing both copies of any twin pair. No upstream file or target statement changes.

## Proved and sorry left

Retirement of already proved modules: 0 original holes, 0 holes closed,
0 holes added, 0 split off, and 0 holes left in the retired modules.
`CochainComplex.tensorPullbackDifferential_shape`,
`CochainComplex.tensorPullbackDifferential_comp`, and
`CochainComplex.isKFlat_pullback` remain provided by the official twin.
The affine twin supplies all six declarations recorded by its node.
No proof becomes `sorry`; existing retained consumer holes remain unchanged.

## No longer needed

`Sheaf.Algebra.Homology.KFlatPullback` and all ten imports of it are removed.
`Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` is an unused duplicate
and is withdrawn too. Neither module has a remaining importer. The nodes
`lem-pc-kflat-pullback-preservation` and
`lem-pc-affine-derived-pullback-tensor-tilde` remain needed and point at the twins;
no mathematical proof dependency or unit step is pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt treated the item as an ordinary zero-hole proof assignment.
The retirement instruction supplies the concrete repair. The hand-off listed 36
consumers; only ten remain in current sources. The other 26 files are already absent.
One of those ten is itself an unused, listed duplicate and is retired in this packet.
The K-flat predicate rename does not require a mathematical proof adaptation.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
