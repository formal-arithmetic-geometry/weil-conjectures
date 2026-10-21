## What changed

Restored `lean/Sheaf/AlgebraicGeometry/LocalizedCartesianFlatSingleComparison.lean`
from its preserved quarantine source, keeping all private helpers, the full public
theorem signature, and its proof. Its proof-only composition import now names
`WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition`, the adopted source
recorded by its existing dependency node.

Repaired the return at head `9e329642cde`: the packet now carries the full
`Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChange` restoration from its
quarantine source, retaining the public `TensorPullback` and `DerivedPullback`
imports added on the current server main branch. Its theorem and proof are
byte-for-byte unchanged. Requested its rework claim on the server; the claim tool
refused because this module is already restored and has no sorry on main. The
included dependency exactly matches that current server source, so no concurrent
restoration work is overwritten. The localized item still requires its recorded
proof-import repair.

Change record: `coord/changes/N2-localized-cartesian-flat-single-restoration.md`.
It lists all 74 consumers, including archived ones. Final lcompile.py compilation passed cleanly for both modules
(4.0 s and 15.9 s) and the unchanged archived direct caller
`CartesianFlatSingleLocalizedBaseChange` (10.7 s). The consumer was compiled in the
same module set against the packet and its scratch copy is excluded from delivery.
The dependency's current public imports are preserved and its interface and proof
are identical. Both import-direction checks pass. No source-library module is
edited.

## Proved and sorry left

This is a zero-hole rework item, not a new proof or decomposition.
The archived item has 0 literal sorries, and the restored item has 0.
`AlgebraicGeometry.localized_cartesian_flat_single_comparison` retains its complete
proof from the recorded dependencies. Its node is
`lem-pc-localized-cartesian-flat-single-comparison`, with the same Lean attachment,
statement, proof steps, and dependency sets.

The adapted dependency also has 0 sorries before and after:
`AlgebraicGeometry.standard_flat_single_baseChange` is unchanged and proved from its
existing mono and epi declarations. Its node is
`lem-pc-standard-flat-single-base-change`.

Holes closed: 0. Holes added: 0. Sorries left in delivered modules: none.
New statements or split-off holes: none. No definitions or statements were changed.

## No longer needed

Removed the stale proof import
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition` from the archived item, replacing
it with its existing adopted source module. The standard comparison retains the
current server's public imports, including
the empty retired wrapper and both adopted source modules; none is removed from
that dependency.

No mathematical dependency, node, or nonempty module is pruned. In particular
`StandardFlatSingleBaseChange` and the preserved cartesian comparison remain needed
by the archived parent. The standard flat base-change, canonical cartesian-source
transport, and localization-comparison route are unchanged. The unit record
`sk-thm-picard-coherence` has empty realized slots, and its approximation/base-change
argument is retained.

## Where the brief, the DAG or earlier work was wrong

The assignment's rework row describes a global-build failure, rather than an open
sorry: the preserved item is already fully proved. The original failure involved
a stale import of a retired duplicate in its
standard comparison dependency. While repairing the return, the server restored
that dependency and added the required adopted source public imports. This packet
retains those newer imports and restores the localized item with its proof-only
composition import repaired. The DAG already records the correct adopted source declarations, so it needs no field edits.
Restoration preserves the archive and its attachment rather than withdrawing it.

LeanFinder found ordinary pullback and composition APIs, Loogle found derived-functor
uniqueness, and grep/local source searches found the existing standard comparison.
No alternative geometric result is needed for this import repair. The original
hypotheses (qcqs p, relative flatness of M, independent localization universes,
and an arbitrary cartesian source) are all preserved; no separatedness, absolute
flatness, or nonempty scheme hypothesis has been added. Zero modules, empty opens,
identity maps, and non-separated qcqs morphisms retain the same proof.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
