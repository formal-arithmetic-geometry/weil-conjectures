## What changed

Replaced the duplicate `Sheaf.AlgebraicGeometry.AffineSpectrumUnitNormalization`
with a forwarding module publicly importing the proved upstream module
`WeilConjectures.AlgebraicGeometry.AffineSpectrumUnitNormalization`. Moved the
existing node's Lean attachment to that upstream declaration. The upstream file
is untouched. Its theorem statement, coherence proof, dependencies and unit route
are exactly those of the quarantined item, apart from the redundant local
irreducibility attribute that caused quarantine. No theorem statement or target
definition changes. There is one public declaration of the normalization theorem.

The former Sheaf import path remains usable. The repair record is
`coord/changes/P8-affine-spectrum-unit-reducibility.md`.
LeanFinder, Loogle and grep confirmed the generic categorical tools; reading the
adopted upstream twin found the complete proof of the exact statement.

Repaired the returned landing of `5d43e3d54b`: re-read the current source,
quarantine entry, node, both dependency declarations and unit record, then rebuilt
the packet on freshly fetched `sheaf-dag` using the delivery tool. This retains
the forwarding repair rather than restoring the obsolete duplicate proof. The
fresh-base dry run `62028e63700` compiled and passed server preflight. The module
also compiled independently in 1.3 seconds; a fresh theorem/axiom check compiled
in 2.1 seconds and printed exactly the three permitted axioms.

## Proved and sorry left

This is a compiler/duplicate repair with zero original holes, zero holes closed,
zero holes added and zero holes left. The node
`lem-pc-affine-spectrum-unit-normalization` is realized by the already proved
`AlgebraicGeometry.affineSpectrum_unit_normalization` in the adopted source library.
A standalone profile of its identical proof reported only `propext`,
`Classical.choice` and `Quot.sound`. No new statements or proof obligations exist.

## No longer needed

The duplicate Sheaf declaration and its private triangle calculation are no longer
needed: the upstream module supplies their complete proof. The former direct
public import of `WeilConjectures.AlgebraicGeometry.AffineSpectrumDirectImageCoordinates`
is supplied transitively by the replacement public import of the upstream
normalization module. Both DAG proof dependencies remain used by that upstream
proof; neither dependency node nor source module is pruned. No source-library
declaration is removed or changed.

## Where the brief, the DAG or earlier work was wrong

The original rework source is preserved in quarantine, and it has no sorry.
Its old `attribute [local irreducible] derivedPullback` is rejected since the
upstream definition is now an `irreducible_def`. Initially removing that line
compiled in 18.3 seconds; profiling the proof and printing its axioms also
succeeded in 23.4 seconds. The delivery probe exceeded 60 seconds, and an attempted
abstract private helper did not improve it. The shortest existing-library route
is to reuse the already proved upstream twin and eliminate the duplicate.

The node's old Sheaf attachment was stale after source adoption. It now points to
the proved upstream declaration, with identical statement, proof and dependencies.
No current Lean source imports the quarantined path, and no consumer needs an
adaptation. `tools/downstream.py` reports the absent Sheaf module as unknown;
a direct source search confirms there are no current imports. The forwarding
module preserves that path for external and restored consumers.

The returned packet passed mathematical review but its landing base was stale.
The required fresh-base dry run now detects the live duplicate declaration and
classifies its replacement as an interface repair for independent review. No
archive is deleted, no declaration is removed from WeilConjectures, and no
dependency or unit step is withdrawn.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
