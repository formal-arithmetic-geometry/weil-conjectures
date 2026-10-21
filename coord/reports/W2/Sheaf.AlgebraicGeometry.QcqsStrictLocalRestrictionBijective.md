## What changed

Retired Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionBijective (the assigned
zero-hole item in coord/retire-items.tsv) and reattached its DAG node to the existing
WeilConjectures.AlgebraicGeometry.QcqsStrictLocalRestrictionBijective theorem.

Adapted its sole direct importer, QcqsStrictLocalRestrictionIsomorphism, without any
public signature or public import change. Its proof now transports to the official
set comparison using the canonical small/full colimit isomorphism and the proved
general ModuleSectionsIsoTransport theorem. The transported representative equations
are checked explicitly; uniqueness gives equality with the bijective set comparison.
The proof cancels the two bijections and uses the concrete module isomorphism criterion.
Updated both nodes' proof routes to match the Lean. Change record:
coord/changes/W2-qcqs-strict-local-bijective-retirement.md.

The adapted module and the unchanged immediate consumer
Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison compiled together through
lcompile.py --all. The unchanged validation copy is excluded from the packet.
#print axioms for
AlgebraicGeometry.Etale.isIso_qcqsStrictLocalRestriction_of_formula reports only
propext, Classical.choice, and Quot.sound. No new theorem or definition is introduced.

## Proved and sorry left

This is a retirement repair with 0 original holes, 0 holes closed, 0 holes added,
and 0 holes left. It is not a decomposition or a newly closed proof hole.
AlgebraicGeometry.Etale.isIso_qcqsStrictLocalRestriction_of_formula has a complete
replacement proof. The adopted
AlgebraicGeometry.Etale.bijective_qcqsStrictLocalRestriction_of_formula remains
unchanged in its official source module. No sorry is left or added by this packet.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.QcqsStrictLocalRestrictionBijective;
its sole private import in QcqsStrictLocalRestrictionIsomorphism is removed.
Also removed the now-unused private import of
WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison from that consumer;
ModuleSectionsIsoTransport supplies the needed proved coefficient compatibility.
No module imports the withdrawn module in the delivered source set.

The small-model isomorphism proof no longer needs the bijectivity wrapper node
lem-weil-pbc-strict-local-module-restriction-bijective: it uses the official set
comparison directly. That node is preserved and attached to its official theorem.
The duplicate's direct colimit glue and explicit uses of
lem-weil-pbc-cofiltered-etale-limit-sections,
lem-weil-pbc-strict-henselization-base-change-cone, and
lem-weil-pbc-qcqs-morphism-permanence are no longer repeated here; the official set
comparison supplies continuity. These nodes and their adopted source declarations
remain needed by the official set proof and are not withdrawn or altered.

SmallStrictLocalSectionMaps and ModuleSectionsIsoTransport remain needed by the
small-model consumer, so they are retained. The adopted source proof instead uses
def-weil-pbc-strict-local-module-sections-set-equiv and
lem-weil-pbc-strict-local-module-sections-set-transport, and its node now records
those dependencies. No further module retirement is asserted.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes proving a sorry, but the current assigned module
already has zero holes. Its explicit retirement row supplies the actual task.
The duplicate and its adopted twin have different Lean types because they use
canonically isomorphic, not definitionally equal, strict-local presentations.
Preserving the direct consumer requires the explicit comparison constructed here;
a bare import swap is insufficient. No mathematical statement is disputed or weakened.
The existing bijectivity node's small-model proof route was appropriate to the
retired copy; it is updated to the adopted source proof. The unit route is preserved.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
