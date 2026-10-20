## What changed

Repaired both modules of the assigned rework cluster by re-exporting their adopted,
completed upstream implementations:
`Sheaf.AlgebraicGeometry.OpenPinnedSourceCounitTriangle` and
`Sheaf.AlgebraicGeometry.OpenPinnedTargetCounitTriangle` now publicly import the
matching `WeilConjectures.AlgebraicGeometry` module.
The two existing DAG nodes now attach to those upstream implementations with
`existing: true`. Their statements, proof steps and dependencies are unchanged:
the upstream files contain the same construction and completed argument.
No source-library file is changed.

Return C-92b3d reconciliation: compared the retained delivery at `92b3d6d1eb`
with the current server branch at `01b064b2068e`. Both Sheaf paths are currently
absent from the branch and preserved under `quarantine/`; the path history
records their removal by upstream-sync quarantine commit `29b1c235f4`. There is
no current active implementation to overwrite. Rechecked the archived files
against the current adopted upstream twins, restored the compatibility imports
against this state, and refreshed both sandbox node copies from the current
server records before changing only their `lean` attachments. The delivery tool
constructs the replacement commit on freshly fetched `sheaf-dag`, rather than
reusing the returned delivery's base `d92f73d8e`.

The quarantined source file differs from its adopted upstream twin only in the
copyright header and its invalid `attribute [local irreducible] derivedPullback`.
The quarantined target file additionally imports the Sheaf source triangle instead
of the upstream source triangle. All public signatures, definition bodies and
proofs otherwise agree exactly. The compatibility modules avoid duplicate public
constants and preserve both old import paths.

Validation after reconciliation: `lcompile.py --all` accepted both final
compatibility modules. A fresh consumer simultaneously imported both Sheaf paths
and both upstream paths, checked all four public declarations, and applied each
triangle theorem at its original full signature from the current node. It
compiled on the server in 5.0 seconds. Its four `#print axioms` commands each
list exactly `propext`, `Classical.choice`, and `Quot.sound`. The consumer is
retained only as scratch text, not as a delivered module. Search was performed
through `msearch.py` (grep, Lean Finder, Loogle) and `rg` on the library. The change record is
`coord/changes/open-pinned-counit-rework-irreducible-20261020.md`.

## Proved and sorry left

This is a zero-hole rework repair. The existing proved declarations are
`AlgebraicGeometry.open_pinned_source_counit_triangle`
(node `lem-pc-open-pinned-source-counit-triangle`) and
`AlgebraicGeometry.open_pinned_target_counit_triangle`
(node `lem-pc-open-pinned-target-counit-triangle`). Both are now reused from the
adopted source tree with precisely their original statements and constructions.
There are zero textual holes before and after the repair, zero holes closed,
zero added, and zero split off. No `sorry` remains in either delivered module.
The axiom checks above also verify that neither reused theorem nor either
comparison definition rests on a hole.

## No longer needed

The duplicate implementations in the two quarantined Sheaf files are unnecessary.
Their declarations remain available with the same names from the upstream twins.
The old direct public imports of
`WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso` and
`WeilConjectures.AlgebraicGeometry.PinnedPullbackCompositionShifts` are supplied
unchanged by the upstream triangle modules. The proof-only source import of
`WeilConjectures.AlgebraicGeometry.AffineSpectrumCompositionCounitSquare` and
proof-only target import of
`Sheaf.AlgebraicGeometry.OpenPinnedSourceCounitTriangle` are unnecessary in the
compatibility files; the upstream proofs carry their own corresponding imports.

The duplicate private source helpers are `mapFactorizationCancel`,
`mappedHomotopyInvHom`, `homotopyCompositionComparison`, `compositionCounit`,
`openCounit`, and `sourceTriangleAlgebra`. The duplicate private target helpers
are `targetHomotopyComparison`, `targetOpenFactor`, and `targetTriangleAlgebra`.
Their upstream counterparts and all proof-dependency nodes remain needed and are
preserved. No DAG node, mathematical dependency or unit route is pruned. No
module is claimed globally unreachable; both Sheaf import paths remain usable.

## Where the brief, the DAG or earlier work was wrong

The assigned module was absent from `lean/` because the upstream sync quarantined
it. `coord/rework.tsv` records the invalid local attribute error. The dependent
target module has the same stale command. The generic brief's outstanding proof
is already complete in both quarantined files and in the adopted source twins.

The literal one-line repairs compiled initially (43.7 seconds for source; a set
compile then took 49.1 and 28.7 seconds), but a delivery compile timed out on the
source. Rather than duplicate and re-elaborate an already proved implementation,
this packet uses the identical upstream construction and theorem. The final
compatibility files avoid the stale attribute and the costly duplicate proof
elaboration, and the explicit consumer verifies their exported declarations.

The DAG's stale Sheaf attachments are updated to the actual upstream declaration
locations. Its mathematical statements and proof plan remain correct. No target
statement, chosen object, geometric hypothesis or upstream declaration changes.

The returned packet had passed review but was not merged because its source path
changed after its base. The current branch has quarantined that path, rather
than retaining a conflicting active proof. This repair restores the required
import path from the current archive, preserves the complete existing proof by
upstream reuse, and repeats the server compilation and signature/axiom checks.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
