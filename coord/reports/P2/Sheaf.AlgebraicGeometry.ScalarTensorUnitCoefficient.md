## What changed

Retired Sheaf.AlgebraicGeometry.ScalarTensorUnitCoefficient in favor of
WeilConjectures.AlgebraicGeometry.ScalarTensorUnitCoefficient, as assigned in
coord/retire-items.tsv and authorized by the 2026-10-20 retirement hand-off.
The full source comparison shows identical public signatures and theorem proofs;
the only differences are the header and a local instance name/formatting.
Reattached lem-sc-scalar-tensor-unit-coefficient to the upstream theorem.
Preserved its statement, proof, proof_deps, parent dependencies and unit route.

Change record: coord/changes/P2-retire-scalar-tensor-unit-coefficient.md.
No upstream source file or target statement changed.

## Proved and sorry left

Closed 0 of 0 holes; added 0 holes; split off 0 statements. No sorry remains
in the withdrawn item. AlgebraicGeometry.Scheme.Modules.scalarTensorCoefficient_unit
is already fully proved, with the identical proof in the adopted twin. This is a
module retirement, not newly proved mathematics.

The original item compiled without warnings in 6.8 seconds. The upstream theorem
was checked by a scratch import and #print axioms in 1.4 seconds; its only axioms
are propext, Classical.choice and Quot.sound. No consumer statements or proofs
are changed by this packet.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.ScalarTensorUnitCoefficient, and its duplicate
implementation and sole public import of
WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations.
The adopted twin retains that import. No mathematical dependency node is pruned.
In particular, lem-sc-scalar-tensor-unit-coefficient remains needed by
lem-sc-scalar-cup-unit-identities and new-sc-scalar-cup-resolution-class-compatibility.
Their references retain exactly the same meaning after the node reattachment.
The unit sk-prop-av-cube has no realized step carried by this duplicate module;
its route and all parent proof dependencies are preserved.

There are zero live Lean importers. The former ScalarCupUnitIdentities consumer
already imports the upstream twin. The other listed consumer,
Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibility, is quarantined and
held by K2 for rework; its archive is preserved. Its archived import of the retired
module must be migrated to the upstream twin when restored. Both uses of
scalarTensorCoefficient_unit have identical signatures in that twin. We inspected
the archived parent rather than inferring mathematical irrelevance from zero live
importers. The retirement request explicitly authorizes withdrawing the duplicate;
the required theorem survives in the upstream twin and its DAG attachment is moved.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief does not describe this item's current zero-hole status.
The specific retirement row supplies the actual task. The historical DIFFERENT
classification now reduces to a differently named local instance and header:
the instance value, theorem signature and complete proof are identical.

A trial compilation of the quarantined consumer with the two obvious import
migrations still encounters an old compiled Sheaf field-linear dependency, whereas
current live sources use the adopted dependency. This is not treated as a theorem
failure, does not justify weakening the parent, and is left to its existing K2
restoration assignment. The quarantine archive, parent declarations and node
attachments are not deleted or replaced by empty modules in this delivery.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
