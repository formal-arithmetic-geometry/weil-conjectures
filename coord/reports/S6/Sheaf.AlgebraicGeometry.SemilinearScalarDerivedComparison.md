## What changed

Repaired the return of c9b5bb33eb9: the original packet overlapped G8's reviewed
0bda340f9cb extraction and proof of `SemilinearScalarOrdinaryComparison`. Started from
the current G8 modules. The pointwise section-normalization correction now belongs to
`SemilinearScalarOrdinaryInterface`, with the corresponding component fields in
`SemilinearScalarRestriction` and `SemilinearScalarAdjunctions` adapted in the same packet.
The restriction construction still proves its level normalization by reflexivity.
Its private transition helper now works pointwise and uses explicit original section
carriers, avoiding a whole-function equality and repeated tower-carrier inference.
G8's ordinary-comparison assembly, uniqueness, and open-congruence proofs are preserved.
The old monolithic file and stale ordinary-node attachment are not resubmitted.

Retained the proof of `AlgebraicGeometry.ProEtale.VaryingRing.scalarD_evaluation`:
identify ordinary direct image on sections, transpose the comparison cube, localize it,
and use compatibility of mates with cubes and the ring-change adjunct equation.
A proved private helper also detects invertibility of `scalarD` through homology.
All public theorem signatures and all existing public definitions in the assigned item
are preserved. No adopted source-library file changes. The formal section-field repair
requires independent statement review; its current owners, users, and edge cases are in
`coord/changes/S6-pointwise-scalar-section-normalization.md`.

## Proved and sorry left

Closed 1 of the assigned item's 2 original holes:
`AlgebraicGeometry.ProEtale.VaryingRing.scalarD_evaluation`.
The original whole-body hole remains in
`AlgebraicGeometry.ProEtale.VaryingRing.derivedScalarComparison`
(node `lem-sf-semilinear-scalar-derived-comparison`).
Added 0 holes and split off 0 statements. All new private helpers are proved.

The adapted component adjunction module retains its one existing hole:
`AlgebraicGeometry.ProEtale.VaryingRing.ordinaryScalarAdjunctions`
(node `lem-sf-semilinear-scalar-adjunctions`). The restriction and interface modules
contain zero holes. Thus the four changed Lean files contain 2 holes in total, only
1 of them in the assigned item. G8's now-proved ordinary assembly and uniqueness are
not reverted to holes. The unchanged proper/open component has its existing hole
`AlgebraicGeometry.ProEtale.VaryingRing.ordinaryScalarProperOpen`; it is compiled as a
consumer and is not changed or counted as newly proved.

Validation: `repair-compile4.log` records exit code 0 for all six modules:
interface 51.3 s, restriction 74.6 s, adjunctions 26.0 s, proper/open 29.2 s,
ordinary assembly 33.7 s, and derived comparison 52.4 s. These are the launcher's
reported elapsed times. The passing source-set key is `51e831d47801ddf98cb962e2`.
A later experimental explicit tower-functor variant was discarded, and the exact
passing source-set hash was verified after restoration. No profiling or diagnostic
options remain in the delivered Lean files. The delivery tool repeats the required
compiler, axiom, consumer, and node checks before push.

## No longer needed

Removed the stale sandbox copy and statement repair of the pre-extraction ordinary
node. Its current G8 attachment and proof route stay unchanged. No library module or
DAG node is withdrawn.

The evaluation proof drops the direct `Sheaf.Paper.SemilinearDerivedSections` import;
its model definitions remain transitively available. It uses
`StrictTowerProperOpenArrows` in place of the broad `StrictTowerProperOpenCalculus`
import and removes the redundant direct `Mathlib.CategoryTheory.Localization.Predicate`
import. Its cube argument needs neither faithfulness of derived evaluation nor
proper-base-change invertibility. The corresponding two obsolete top-level `tool_uses`
entries are removed from the derived node. The original unfinished theorem's alpha
and open-mate steps remain explicitly marked as a plan. No whole-library pruning claimed.

## Where the brief, the DAG or earlier work was wrong

The previous packet used the old monolithic ordinary module and would have overwritten
G8's intervening reviewed work. That conflict is repaired at the actual new interface
owners, with the proven current restriction, congruence, assembly and uniqueness retained.
The two component interfaces must agree with the assembled package's pointwise
normalizations; repairing only the extracted top-level structure would break its assembly.

Whole-function heterogeneous equality did not provide the intended pointwise identities
without an independent carrier equality. The formal interface strengthening is disclosed
in the three statement-change records. Their mathematical section prescription is the
same identity map, and all current node citers are listed.

The earlier attempt to close the second original theorem did not compile: ordinary alpha
normalization repeatedly exceeded kernel checking limits on chosen pullbacks and adjoints.
Those candidate proofs remain excluded; no uncompiled candidate is counted as a proof.
This repair addresses the actual returned overlap and preserves the completed evaluation
argument. All compilation uses `lcompile.py`; no launcher or budget metadata is edited.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
