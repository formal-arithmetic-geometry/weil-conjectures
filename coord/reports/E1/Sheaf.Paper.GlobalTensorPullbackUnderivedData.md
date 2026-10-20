## What changed

Repaired every point of return C-03a5b (head 03a5bf890).
Restored `lean/Sheaf/Paper/GlobalTensorPullbackUnderivedData.lean` from the
archived quarantine implementation, preserving its theorem statement and proof.
The sole substantive archive edit replaces
`public import Sheaf.Algebra.Homology.KFlatPullback` with
`public import WeilConjectures.Algebra.Homology.KFlatPullback`.
Wrapped the six named local instance declarations immediately after their colons;
every line is at most 100 characters.

Reverted the node's Lean attachment to `existing: false`, module
`Sheaf.Paper.GlobalTensorPullbackUnderivedData`, and file
`lean/Sheaf/Paper/GlobalTensorPullbackUnderivedData.lean`. The resulting node
matches the current repository record; statement, dependencies, proof route,
source, and unit are unchanged. Dropped the rejected change record
`coord/changes/global-tensor-pullback-underived-upstream.md`.
The quarantine archive and all adopted source-library modules remain untouched.

The first dry run required an accurate record for the public-import replacement.
Added `coord/changes/global-tensor-pullback-underived-kflat-import.md`, documenting
the actual archive repair and quarantined consumer. The rejected upstream
re-export record remains dropped.

Validation: the restored module compiles without errors or warnings. An import
probe checks it together with `Sheaf.Paper.ModuleCupNaiveMap` and prints the
axioms of the restored theorem: exactly `propext`, `Classical.choice`, and
`Quot.sound`. Both files compile cleanly (6.4 seconds and 1.3 seconds).
The probe is scratch work, not a delivery module.

## Proved and sorry left

Zero original holes, zero holes closed, zero holes added, zero split off.
`AlgebraicGeometry.Scheme.Modules.exists_globalTensorPullback_underived_data`
(node `lem-sc-global-tensor-pullback-underived-data`) retains the archive's
complete proof. No sorry remains in this item or is introduced elsewhere.
This is the assigned zero-hole quarantine repair, not a new proof or decomposition.

## No longer needed

Replaced the obsolete `Sheaf.Algebra.Homology.KFlatPullback` import with its
adopted `WeilConjectures.Algebra.Homology.KFlatPullback` path.
Removed the rejected re-export of
`WeilConjectures.AlgebraicGeometry.GlobalTensorPullbackUnderivedData`.

All other archived imports are retained and used. In particular, the statement
uses the cup map in `Sheaf.Paper.ModuleCupNaiveMap`, and the proof invokes
`Sheaf.Paper.GlobalTensorPullbackMonoidalNormalization`, as the node records.
No DAG node or module is pruned or withdrawn. The quarantined parent
`Sheaf.Paper.ModuleCupGlobalTensorPullback` imports both the cup-map module and
this item; its unrelated K-flat import repair remains its own rework assignment.

## Where the brief, the DAG or earlier work was wrong

The previous upstream re-export was incorrect. Matching printed declaration
names and formulas did not establish interoperability: its cup-map and monoidal
normalization declarations came from the WeilConjectures copies rather than
the Sheaf declarations recorded by the dependency nodes. Importing it with
`Sheaf.Paper.ModuleCupNaiveMap` caused a declaration conflict, including in the
parent. The previous change record's assertion that the parent retained a
working import path was false. Restoring the archive with the requested K-flat
import correction repairs that error without changing the mathematical route.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
