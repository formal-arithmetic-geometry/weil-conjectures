## What changed

Restored `lean/Sheaf/AlgebraicGeometry/SmoothProperTensorPerfectCaseCore.lean`
as a public compatibility import of the adopted source module with the same suffix.
The archive and all WeilConjectures files remain untouched. Updated the core node's
Lean attachment to the existing source declaration, with its actual signature.
The source theorem has the entire archived conclusion, without the redundant earlier
hm/ha hypotheses; it still quantifies over every monoidal structure and adjunction.
Its proof constructs the canonical projection by conjugation, composes tensor-Hom
bijections, identifies the counit mate and applies Yoneda, exactly as the existing
node specifies. Its three proof dependencies are retained.

Change record: `coord/changes/B6-smooth-proper-tensor-perfect-core-source.md`.
This resolves the recorded duplicate-pullback import failure and avoids introducing
a second public declaration with the same name as the adopted source.

## Proved and sorry left

The quarantined item had **zero** sorries. Holes closed: none (0 of 0).
Holes added: none. Sorries left in the delivery: none. No decomposition or new node.
`AlgebraicGeometry.smoothProper_tensor_perfect_case_core` already has its complete
proof in the adopted source; the restored path re-exports that proof.

Validation includes a server compile of the complete unchanged source proof and a
separate server check applying it to the exact archived statement, including hm/ha.
The source copy compiled in 4.4 seconds, the archived-signature application in 3.0
seconds, and the restored bridge in 1.3 seconds, without warnings. The axiom probe
for the source theorem reports only propext, Classical.choice and Quot.sound.
The import-direction check permits the bridge, and a full DAG scan finds no node
referencing this core in stmt_deps, proof_deps or proof-step uses.

## No longer needed

The duplicate local public theorem body and private projection_isIso helper are
replaced by the source theorem and its already-proved private helper.
The old direct import of `Sheaf.AlgebraicGeometry.DerivedPullback` is removed; the
source proof uses the adopted canonical pullback. All other old direct imports are
supplied through the source core's public/proof imports instead of being repeated
in the compatibility module: PerfectComplex, SchemeDerivedDirectImage,
DerivedTensorStructure, Mathlib Proper, Noetherian, ChangeOfRings, Monoidal.Basic,
Projective, Tor, PerfectTensorHomDuality, MonoidalProjectionConjugate,
PerfectRightAdjointTensorHomComparison and Yoneda.
No mathematical dependency node is pruned: the duality, conjugation and tensor-Hom
comparison remain needed by the source proof. The restored module is retained as
an import bridge, not withdrawn or replaced by an empty module.

## Where the brief, the DAG or earlier work was wrong

The item is a zero-hole rework repair, not an unproved comparison theorem. The
upstream sync already adopted its complete proof, while the node still pointed at
the quarantined twin. The archive alone has two additional unused binders hm/ha;
the current source parent already calls the stronger adopted signature without them.
The attachment now matches that source, and the full old obligation is checked as
a consequence. Zero live importers was not used as a reason to erase the node or
its dependencies: both the archive and all three proof dependencies are preserved.
No active return entry exists for B6. No consumer adaptation is necessary.

Searches: repository rg found the source theorem and sole source parent; LeanFinder
returned generic tensor-adjunction results, and Loogle returned conjugateEquiv_iso
and related mate lemmas. The configured Mathlib grep had no theorem-name match.
The source proof already uses those categorical tools, so it is the shortest route.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
