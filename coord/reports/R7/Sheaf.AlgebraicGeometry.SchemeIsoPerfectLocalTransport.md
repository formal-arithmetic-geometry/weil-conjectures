## What changed

Repaired the quarantined module by restoring it as a public re-export of the proved
`WeilConjectures.AlgebraicGeometry.SchemeIsoPerfectLocalTransport` twin. This reuses
`AlgebraicGeometry.Scheme.scheme_iso_local_perfect_transport` without duplicating
its declaration or private restriction-square proof. Updated the existing DAG node's
Lean attachment and verbatim signature to the official declaration.
Change record: `coord/changes/scheme-iso-perfect-local-upstream-reexport.md`.

Repair of return C-51bdc: compared the retained delivery 51bdc8996a with the current
shared branch. The live Sheaf module is still absent and the original is retained
under quarantine; the current upstream theorem and quarantine record were reread.
The restored re-export and updated Lean attachment remain the required repair.
The delivery tool regenerates this packet on current `origin/sheaf-dag`, rather
than reusing the returned delivery's stale base d92f73d8e. No current source edit
is overwritten.

## Proved and sorry left

This is a zero-hole quarantine repair: 0 original holes, 0 holes closed, 0 holes added,
0 split off, and no remaining sorry. The upstream theorem
`AlgebraicGeometry.Scheme.scheme_iso_local_perfect_transport` is already proved.
Fresh server compiles pass for the restored module (1.2 s) and a separate generic
consumer example (0.1 s). The example proves the
inverse equivalence preserves perfectness through the restored Sheaf import.
The imported transport theorem's axiom check lists only `propext`, `Classical.choice`
and `Quot.sound`. No arbitrary object is chosen from an unproved existence theorem.

## No longer needed

The Sheaf module no longer needs its duplicate `localRestrictionSquare` or duplicate
public transport declaration. Its direct imports of
`WeilConjectures.AlgebraicGeometry.PerfectComplex`,
`WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect`, and
`WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedRestrictionSquare` are replaced
by the upstream twin import. These dependencies remain used by the upstream proof;
no DAG proof dependency or upstream module is pruned. No new node is needed.

## Where the brief, the DAG or earlier work was wrong

The assigned live Sheaf file is absent: coord/rework.tsv records its quarantine after
an upstream-sync universe inference failure at line 171. The quarantined theorem
already has a complete proof, so this is a compilation repair, not a new proof task.
A fresh lcompile run of the unmodified quarantined file reproduced exactly the
reported line-171 universe constraint failure. This retry recompiles the replacement
and generic consumer against the current published server build, with the restored
module supplied as a sandbox dependency. The axiom check again contains only the
three permitted axioms.
The official upstream twin already corrects the implicit overFunctor universes and
proves the exact local-transport result. The DAG still pointed to the quarantined
copy; it now points to the official theorem, retaining the same proof route.
The unit's realized statement and step lists are empty; no unit route is bypassed.
Current source scanning finds no importer of the Sheaf path, hence no consumer edit
or forced adaptation is required. Search services returned general equivalence and
complex-support lemmas, with no more specific Mathlib theorem; the source-library
search found the complete upstream proof used here.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
