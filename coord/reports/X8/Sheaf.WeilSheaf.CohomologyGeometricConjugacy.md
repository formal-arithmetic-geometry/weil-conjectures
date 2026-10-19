## What changed

Found the exact theorem already proved in
`WeilConjectures.WeilSheaf.CohomologyGeometricConjugacy`, with the same fully qualified
name, universes, hypotheses, and conclusion. Its source implementation also defines
`cohomologyLinearEquivOfGeometricFiberIso` and exposes the comparison API needed by
the complete proof. Reuse that source implementation rather than duplicating it.

Withdraw `Sheaf.WeilSheaf.CohomologyGeometricConjugacy` and
`Sheaf.WeilSheaf.CohomologyGeometricEquivalence` using deleted.txt. In their only
external direct consumer, `WeilConjectures.WeilSheaf.PoincareDuality` (unclaimed),
replace the private Sheaf conjugacy import with the corresponding source-library
import. No consumer signature or proof body changes. Attach both existing nodes to
the corresponding existing source declarations; update the conjugacy proof plan to
name the actual composition, carrier, and power comparisons used in that proof.

Change record: `coord/changes/X8-geometric-cohomology-source-reuse.md`, including the
old definition and theorem verbatim and the complete consumer table. No target type,
unit statement, or unit proof route changes. This is the shortest-route reuse of an
already proved library result, with duplicate removal as required by brief step 8d.

## Proved and sorry left

The sole assigned hole,
`AlgebraicGeometry.WeilSheaf.cohomologyLinearEquivOfGeometricFiberIso_map_frobenius`
(node `lem-pod-cohomology-geometric-conjugacy`), is retired in favor of the existing
complete proof of the exact theorem in the source library. One hole removed by reuse;
zero new holes; zero split-off statements. Both withdrawn modules contain no remaining
declarations after landing. The equivalence is an actual derived-global-section
construction, not data obtained from a bare existence theorem.

The retained proof inverts the given geometric conjugacy, uses
`derivedGlobalSectionsUnitIso_trans`, applies homology, and conjugates by
`cohomologyCarrierIso`. Its power comparison is proved by induction, with the case
r = 0 using identity transport and the successor case using composition. This is a
proof already present in the library, not an assertion that two unrelated operators
are equal. The delivery does not claim to have written that existing proof anew.

Unchanged holes in the adapted PoincareDuality consumer:
`AlgebraicGeometry.WeilSheaf.exists_traceCup_isPerfect` (pre-existing upstream obligation, unchanged). No hole is added or
removed in that consumer.

## No longer needed

Pruned modules:
- `Sheaf.WeilSheaf.CohomologyGeometricConjugacy` (duplicate of the proved source theorem).
- `Sheaf.WeilSheaf.CohomologyGeometricEquivalence` (duplicate canonical construction).

Removed imports with the withdrawn modules:
- `Sheaf.WeilSheaf.CohomologyGeometricEquivalence`.
- `Sheaf.Paper.CommonStageCompactWeilCohomology`.
- `Sheaf.Paper.ConstantWeilStructure`.
- `Sheaf.Paper.PointProEtaleSectionsExact`.
- `Sheaf.SixFunctors.FrobeniusCohomologyTransport`.
- `Sheaf.Paper.GlobalGeometricFrobenius`.
- `WeilConjectures.WeilSheaf.CohomologyExact` (the duplicate equivalence's direct import;
  the retained source implementation still needs the actual source cohomology API).

The source proof needs no separate dependency on
`def-weil-frobenius-cohomology-transport`,
`lem-weil-point-proetale-sections-exact`, or
`def-weil-constant-weil-structure`: the source files prove the specialized transport,
composition, exactness and Frobenius comparisons for the actual source adic unit.
`def-weil-ordinary-compact-cohomology` and
`def-weil-global-geometric-frobenius` are likewise not additional proof dependencies
of the conjugacy theorem; their statement-level roles are unchanged. The retained
proof depends on `def-pod-cohomology-geometric-equivalence`, now attached to the source
construction. The equivalence node's original construction dependencies are retained.
The two nodes are preserved and reattached, not deleted. No claim is made that the
other removed proof-import modules become globally unreachable: other consumers
may still need them.

## Where the brief, the DAG or earlier work was wrong

The assigned obligation duplicates a complete result already in the source library.
The old statement modules used identical fully qualified names for a local older
construction and a holed compatibility theorem, hiding the reusable source API.
The source equivalence is precisely homology of derived global-section transport
conjugated by the carrier identifications, as required by the node. Both signatures
match the old signatures; no restriction on r, choice of embedding, or relation
between the two finite fields is introduced.

Earlier attempts were blocked by unavailable published dependencies and intermittent
compile-server failures. On this resumption, the required `deliver3.py --no-push`
succeeded: dry-run commit `c17b92be7b` compiles and passes preflight, classified CODEX
for independent review. The earlier compile-service blocker is resolved.

Rechecked against the current shared sources: the consumer diff is exactly one
private import replacement; both source declarations have byte-identical signatures
to the withdrawn declarations and both source modules have zero textual sorries.
The replacement import passes `tools/import_direction.py may`. Only the permitted
node fields differ, and each node's proof dependencies equal the union of its
proof-step uses. The unit statement and proof route are preserved.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
