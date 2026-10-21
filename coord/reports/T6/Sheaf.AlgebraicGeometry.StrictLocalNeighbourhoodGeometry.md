## What changed

Retire the assigned zero-hole Sheaf.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry
copy in favour of the official WeilConjectures module. Redirect its DAG attachment.
The official structure uses strictLocalization; the old consumers use the small
coordinate-ring colimit. New StrictLocalSmallModel.NeighbourhoodGeometry constructs
the canonical pullback isomorphism and transports the official cone, its limit proof,
and both specified projection equations. Adapt consumers to that proved API.
The existence helper reuses the complete official existence theorem.

Change record: coord/changes/T6-retire-strict-local-neighbourhood-geometry.md.
The record lists the 27 live downstream modules, their source changes or unchanged
checks, and the historical/quarantined parents. No upstream file is edited.

## Proved and sorry left

The assigned module originally had zero sorries. Holes closed: none (0 of 0).
Holes added: none; split off: none. No sorry remains in any delivered module.
This packet implements retirement and canonical-definition compatibility repair.

The canonical transport module compiles with lcompile.py in its supported remote mode
(LCOMPILE_NO_LOCAL=1). The local published mirror initially lacked the upstream module's
.olean.server companion; remote compilation resolves that artifact and checks the proof.
The resumed attempt repaired the missing explicit HasColimit instance and used the
cone/cocone projection simp API in the first-component comparison proof.
The published mirror subsequently acquired the missing artifacts. All 11 changed/new modules
compiled without errors or warnings in the complete changed-source check. The slowest
consumer took 50.9 seconds, below the unchanged 60-second limit. An additional check
compiled 18 unchanged/changed downstream modules before the existing unchanged
StrictLocalLocalizedHomGerm source exceeded 60 seconds. Exploratory optimization of
that unrelated proof was discarded; it has no use of the migrated geometry API and
its original source and public signatures are retained. This packet contains only
11 changed/new modules, all of whose adapted consumers compiled successfully.

Delivery is blocked by the launcher execution, not by a Lean diagnostic. Repeated
required deliver3.py runs terminated with exit code 143 (SIGTERM), without producing
a preflight result or DELIVERED line. The final unbuffered retry printed the priority
retirement slot-pool announcement and then was also terminated. No successful push
is claimed. All 11 changed/new modules had already compiled without errors or
warnings in the completed lcompile.py --all check. The packet is retained intact.

Proved constructions and equations:
AlgebraicGeometry.Etale.strictLocalSmallModelPullbackIso;
AlgebraicGeometry.Etale.StrictLocalNeighbourhoodGeometry.smallModelLegs,
smallModelIsLimit, smallModelOver, smallModelFirst.
The existing smallModel_nonempty_strictLocalNeighbourhoodGeometry remains fully proved
from the official nonempty_strictLocalNeighbourhoodGeometry theorem.

## No longer needed

The assigned Sheaf.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry module is retired;
its four duplicate declarations are supplied by the official module, and its DAG
attachment is redirected. Both live direct importers stop importing the retired copy. Consumers using the
transported API explicitly import its module; the complex-mate proof additionally
imports the adapted underived-mate proof API.
The existence helper removes its private imports of
WeilConjectures.AlgebraicGeometry.StrictHenselizationBaseChangeCone and
Mathlib.AlgebraicGeometry.Morphisms.Affine. Its dependency on
lem-weil-pbc-strict-henselization-base-change-cone is replaced by reuse of the proved
official existence theorem and the proved small-model transport API.
No source-library declaration or module is deleted. No blueprint unit step is pruned.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a proof item, but coord/queue.tsv and coord/retire-items.tsv
assign this zero-hole module for retirement. The retirement table's three consumers
predate the restored StrictLocalSmallModel chain: the current live direct importers
are StrictLocalCohomologyGerms and StrictLocalSmallModel.StrictLocalNeighbourhoodGeometryExistence.
The old archived direct importer remains preserved; its node now attaches to the adapted
restored helper. Absence of the archived file from lean/ was not treated as withdrawal.

Import replacement alone is invalid: the old and official structures have different
cone vertices. The canonical comparison proves that their specified legs correspond;
no existing cohomology object or target statement is replaced by a different one.
The new bridge uses the already proved structural-map clause of the off-unit node
lem-weil-pbc-strict-henselization-small-closed-fiber-comparison as a general comparison
tool, without using its fibre assertion or bypassing any unit route.

Edge cases: the transport needs no qcqs hypothesis on f; it works for empty X, affine
bases, field bases, and arbitrary geometric points. It uses only pullback functoriality
and the canonical colimit coprojection identity, so imposes no nonemptiness on X.

## New nodes

lem-weil-pbc-strict-local-small-model-geometry-transport records the complete canonical
pullback-isomorphism and transported-limit API in
Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry. It is fully proved,
not a split-off hole; its source is Tag 03Q9's affine-neighbourhood limit argument and
the existing inverse-colimit comparison formula. Mathlib searches found the general
pullback-map, final-colimit and cone-transport tools, which are used in the proof.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
