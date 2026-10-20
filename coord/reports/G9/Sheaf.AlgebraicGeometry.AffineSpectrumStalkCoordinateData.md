## What changed

Restored `Sheaf.AlgebraicGeometry.AffineSpectrumStalkCoordinateData` from its current
quarantined source and replaced its public import of
`Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition` with
`WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition`.
The upstream condition and the existing upstream source-transport proof import now
load the same tensor-model declarations, fixing the duplicate declaration error.
Every declaration, signature, proof, docstring, and other import is preserved exactly.

Repaired the return at branch head `e332a34a86`, whose delivery base was `e0d550965`:
read the current return and rework records, rebuilt the sandbox module from the current
shared source, and reapplied the import replacement. The active library path is absent;
the current source is the archive recorded in `coord/rework.tsv`, at
`quarantine/Sheaf/AlgebraicGeometry/AffineSpectrumStalkCoordinateData.lean`.
An exact text comparison verifies that only the public import differs from this source.
The delivery tool prepares the new packet on its current fetched `sheaf-dag` base.

Fresh remote validation through `lcompile.py` reproduces the unmodified source's duplicate
`ModuleCat.BaseDerivedTensorCohomologyModel._sizeOf_inst` error (0.8 seconds).
An ordered compile of the repaired source, an axiom probe, and the unchanged current
quarantined direct consumer succeeds without errors or warnings (0.1 seconds per file).
All validation copies are under `scratchpad/`, outside the delivered `lean/` tree.
Change record: `coord/changes/affine-spectrum-stalk-coordinate-upstream-import.md`.
No DAG edit is needed because the existing statement and complete proof route are retained.

## Proved and sorry left

Zero-hole compatibility repair: 0 original holes, 0 holes closed, 0 holes added,
0 split off, and 0 holes left. No declaration is left with `sorry`.
`AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_stalk_coordinate_data`
(node `lem-pc-affine-spectrum-stalk-coordinate-data`) retains its complete existing proof.
Its axiom probe reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The actual stalk-ring equivalences and all private helpers are preserved.

## No longer needed

Removed import: `Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition`.
Its upstream counterpart supplies the canonical stalk rings, algebra maps, tensor map,
stalk complex, and tensor-pullback additivity required by the statement and proof.
No mathematical dependency node or whole module is pruned or withdrawn.
The source-transport and adjunction proof imports remain needed.
The unit `sk-thm-picard-semicon` has empty realized statement and proof-step arrays;
this import migration preserves its route.

## Where the brief, the DAG or earlier work was wrong

The latest return reports a stale-base landing conflict, not an incomplete proof.
The repair was reapplied to the current preserved source and all relevant compiler
checks were repeated. This item is a zero-hole upstream-sync rework. The earlier sync
migrated its source-transport import to upstream while leaving the local stalk-condition
import, so both copies of the tensor model were loaded. The mathematical statement and
proof plan need no correction.

The retained LeanFinder, Loogle, and grep searches found the existing stalk-isomorphism
and affine-spectrum naturality APIs used by the proof. No new lemma or node is needed.
`downstream.py --allow-missing --uses exists_affineSpectrum_stalk_coordinate_data` reports
zero active importers and users. Searching both `lean/` and `quarantine/` finds the single
quarantined direct caller `AffineSpectrumTensorCoordinateData`, currently unclaimed.
Its unchanged source compiles against the repair. The new upstream import creates no
import cycle. No forced adaptation or source-library edit is needed.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
