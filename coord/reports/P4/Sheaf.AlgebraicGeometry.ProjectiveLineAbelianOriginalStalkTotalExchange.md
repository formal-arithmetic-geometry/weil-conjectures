## What changed

Restored the quarantined module
`Sheaf.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange` and repaired
its imports and proof for the current library. The original signature of
`AlgebraicGeometry.Etale.projectiveLine_abelian_originalStalk_totalExchange` is
byte-identical to the archive, including its small strict-henselization model.

The structural-map public import now names its adopted WeilConjectures owner.
The localization private import also names the adopted owner. Its canonical-model
inputs are obtained by composing eA and eB with Spec of the inverse
`smallStrictHenselizationColimitIso`. The existing theorem
`smallStrictHenselizationColimitIso_toBase` proves equality of their structural
composites. Explicit equalities transfer hphi, hrhoA, hrhoB and the projective-line
pullback square. The original c1.trans b1, c2.trans b2 assembly then proves the
same exchange equation. The comparison import is private; only its structural-map
equation is used, not its closed-fibre conclusion.

The item node retains its Lean attachment and all three proof dependencies and adds
the existing small/full structural comparison. Its proof and origin describe the
actual transport. The localization node's stale Lean attachment is corrected to
its existing adopted implementation; the old Sheaf module is already empty.
No source-library file, existing definition, statement, target or unit route changes.
No new module other than restoration of the assigned item is delivered.

Change record: `coord/changes/P4-original-stalk-model-restoration.md`.

## Proved and sorry left

This is a zero-hole rework item: 0 textual holes before, 0 after; 0 holes closed,
0 holes added, 0 split off. The restored theorem
`AlgebraicGeometry.Etale.projectiveLine_abelian_originalStalk_totalExchange`
has a complete compiling proof. No declaration with sorry is left or added by this
packet. Existing dependencies are used as stated; no new obligation is handed on.

The repaired item compiles without warnings in 10.0 seconds, and compiled again as
part of the consumer check in 13.3 seconds. The archive signature was compared
byte-for-byte and all Lean lines are at most 100 characters. Import-direction checks
for both new proof imports pass.

Consumer census includes quarantined sources: the only direct Sheaf importer is
`Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange`.
Its unchanged archive fails independently on the same retired public structural-map
import (the names exist but are imported privately). Its application of this theorem
uses exactly the preserved original signature. A scratch consumer probe replaces
only that already-retired public import with the canonical upstream structural-map
import, leaving its entire statement and proof unchanged; it is checked against the
restored item. The scratch consumer compiles without warnings in 20.3 seconds.
The accompanying `#print axioms` reports exactly `propext`, `Classical.choice` and
`Quot.sound` for the restored theorem, with no further axiom. This independent
consumer repair is not part of the packet.

Edge cases remain unchanged: q=0, zero coefficients, arbitrary pullback models and
purely inseparable extensions of separably closed fields all pass through the same
existing localization and strict-local theorems. Transport changes neither A, B,
phi, the residue maps, G0 nor the cohomology map; no torsion or finiteness condition
is added.

## No longer needed

Removed imports of the already-withdrawn, empty wrappers
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap` and
`Sheaf.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization`.
Their adopted WeilConjectures owners replace them. All other original imports are
retained and the new private comparison import supplies the structural equality.

No mathematical dependency, node or module is globally pruned. The item's three
original proof dependencies and its unit route are retained; the canonical-model
transport adds the existing node
`lem-weil-pbc-strict-henselization-small-closed-fiber-comparison`.
The archived file and its parent remain preserved; no withdrawal is requested.

## Where the brief, the DAG or earlier work was wrong

The queue's repair label is accurate, but there are no proof holes in the archive.
Restoring it verbatim is insufficient: its public structural-map wrapper and private
localization wrapper have both been retired. The archived statement uses
`strictHenselizationScheme` and `strictHenselizationStructuralMap`; the adopted
localization statement uses `strictLocalization` and `strictLocalizationToBase`.
They are canonically isomorphic over the base, not definitionally interchangeable.
The old inputs therefore need the explicit colimit-model transport now supplied.

The localization node still pointed to its already-empty Sheaf module. Its repaired
attachment records the adopted theorem actually invoked. Its abstract mathematical
statement and proof route are unchanged. The item's own attachment is preserved.

`tools/downstream.py` cannot enumerate a quarantined item and reports it unknown;
source searches of both the current and archived Lean trees supply the consumer
census instead. The archived parent's independent retired-import failure is recorded
above; it is not caused by a signature change in this restoration.

LeanFinder, Loogle and Mathlib grep were run through msearch.py. Finder returned
only topological-stalk or module-restriction results; Loogle had no matching
cohomologyMap identifier; grep found no strict-henselization/stalk result. Repository
search found the adopted theorem, the canonical localization interface and the
already-proved small/full structural comparison, so no new lemma is needed.

A read-only DAG traversal also encountered the pre-existing cycle through
`lemma-weil-pbc-derived-exchange-replacement`,
`lem-weil-pbc-derived-exchange-termwise`,
`lem-weil-pbc-derived-exchange-unbounded-transport` and
`lem-weil-pbc-derived-exchange-bounded-comparison`. Those nodes and edges are
unchanged. The sole added structural-comparison dependency does not reach this
item, so it introduces no cycle. Both Lean import-direction checks pass.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
