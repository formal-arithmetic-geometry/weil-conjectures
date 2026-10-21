## What changed

Restored `lean/Sheaf/AlgebraicGeometry/StandardSingleBaseChangeMap.lean` from its
quarantine archive. The current `coord/rework.tsv` assigns this missing definition
for restoration; `coord/queue.tsv` identifies it as a root with 113 quarantined
importers waiting. This restores the actual declaration, not an empty module or
a withdrawal. The archive and its DAG attachment are retained.

`AlgebraicGeometry.standardSingleBaseChangeMap` is the canonical derived
base-change mate on `M[0]`, followed by direct image of
`AlgebraicGeometry.Scheme.picardTermwiseSingleMap`. Its full type, actual
construction, universe, visibility, docstrings and three public imports are
identical to the archive. The existing termwise map uses the pinned universal
left-derived counit and the unique adjunction-preserving pullback comparison.
No independent witness or comparison is introduced.

Read the existing node, all statement-dependency records, both proof-dependency
declarations, and `sk-thm-picard-coherence`. The construction follows the node's
two steps without changing the unit route. Checked Stacks Tags 08HY, 0A1D and
0DJ9 in the local literature. Zero modules in the current Lean tree import the
absent file; the archived direct consumers and declaration users are recorded
in `coord/changes/E1-standard-single-base-change-map-restoration.md`: eleven
direct importers and eighteen declaration users including indirect consumers.
Sixteen other DAG nodes cite the definition in statement dependencies, proof
dependencies or proof steps; their references are also retained. Their
interface and construction are restored verbatim, so none needs adaptation.

Mathlib searches through `msearch.py` (Lean Finder, Loogle and grep) found no
replacement for this derived scheme comparison. Current-library searches found
the existing general `singleDegreeBaseChangeComposite`, which uses an explicit
family of derived-category and additive instances. Replacing the existing
definition with that interface would not simplify this restoration or preserve
its current public-import contract.

## Proved and sorry left

The assigned definition repair has zero holes before and after restoration.
`AlgebraicGeometry.standardSingleBaseChangeMap`
(`def-pc-standard-single-base-change-map`) is a concrete composite and has no
`sorry`. Holes closed: none (0 of 0). Holes added: none. Split-off statements:
none. No declaration beyond the archived original, new node or axiom is
introduced. After the dependency publication completed, the restored module
compiled cleanly with `lcompile.py` in 2.6 seconds (exit 0).

## No longer needed

None. All three public imports and both recorded proof dependencies remain
needed. In particular `PicardTermwiseSingleMapComposition` supplies the actual
termwise map used in the definition; it has not been bypassed or restated.
No module is withdrawn, no DAG dependency or Lean attachment is removed, and
no unit statement or proof step is pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an item with holes, but the current rework
assignment is restoration of a quarantined, already concrete definition. Its
absence from `lean/` is not a withdrawal. The first compile found that the
already-restored `PicardTermwiseSingleMapComposition` source was not yet present
in the published compiled library; this is publication lag, not a statement
error or a reason to duplicate its declarations. No mathematical error was
found in this definition or its node.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
