## What changed

Restored `lean/Sheaf/Paper/CondensedQbarComparisons.lean` from its explicit rework archive.
The live path was missing after the cluster restore. All four public concrete definitions,
their types, bodies, imports, and docstrings are token-identical to the archive; fourteen
long lines are wrapped so the restored module compiles without warnings. The existing node
`def-weil-pbc-qbar-condensed-comparisons` remains attached to all four definitions. Its
`lean.statement` text now records the already-archived `h.asOver (Spec (.of k))` argument.
No mathematical statement or dependency is changed.

Change record: `coord/changes/H4-restore-condensed-qbar-comparisons.md`.

The archived source compiled successfully with fourteen line-length warnings. The restored
source compiled cleanly in 11.6 seconds through `lcompile.py`. A `--all` overlay
compile also built the restored module in 12.8 seconds. The full archived
`CondensedQbarExchangeRightAdjunct` scratch consumer timed out at 60 seconds, both during
artifact compilation and in a single-file diagnostic run with `set_option profiler true`.
The timeout tool discards partial profiler output, so no declaration-level profile was
available. This is recorded as an unresolved limitation of that separate quarantined rework
item, not as a passing consumer check. The delivery preserves every token of the comparisons
archive, so no new reduction behavior or consumer adaptation is introduced.

A separate importer using only `public import Sheaf.Paper.CondensedQbarComparisons` checked
all four original public result types and applied the corresponding restored definitions.
It compiled cleanly against the overlay in 4.4 seconds. Both scratch consumer sources are
retained under `scratchpad/`, outside the delivered `lean/` tree. The downstream tool with
`--allow-missing` reports zero live importers and zero live declaration users; the five
quarantined direct importers are enumerated in the change record.

## Proved and sorry left

This is an assigned zero-hole restoration. Original holes: 0. Holes closed: 0. Holes added: 0.
Remaining holes: 0. No theorem is split off.

The four restored definitions are
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbarPullIso`,
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbarPushHom`,
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbarSourceHom`, and
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbarTargetHom`.
Their data are the explicit restricted ambient comparisons and their composites, with no
hollow definition or arbitrary choice from a mere existence theorem. Existing upstream proof
dependencies may still have holes; this delivery adds none and claims no transitive closure.

## No longer needed

None. No import, declaration, module, DAG dependency or unit route is pruned. In particular,
the five quarantined parent modules still import this module and their DAG nodes still cite
its node; the lack of current live Lean importers does not justify withdrawal.

## Where the brief, the DAG or earlier work was wrong

The item has zero `sorry`s and is a missing-module rework assignment, not an unfinished
comparison theorem. The archive already uses the current bundled-over-category interface.
The item's compiler findings are fourteen line-length warnings, fixed by whitespace wrapping.
The node's `lean.statement` had omitted this existing `asOver` spelling; the textual attachment
is refreshed without changing its mathematical statement. No defect of the four constructions
or of their specified direction was found. Their node has no proof steps to split.

LeanFinder and Loogle confirm `ObjectProperty.isoMk` as the direct full-subcategory constructor;
local Mathlib source confirms `homMk` and `isoMk`. The current library already supplies
`derivedPullIso`, `derivedPushHom`, the scalar-extension functor, and the bounded restrictions,
so no alternative definitions or new helper statements are needed.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
