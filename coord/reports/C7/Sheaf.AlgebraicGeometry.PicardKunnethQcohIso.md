## What changed

Restored lean/Sheaf/AlgebraicGeometry/PicardKunnethQcohIso.lean from the exact archive
listed in coord/rework.tsv. Replaced its obsolete public import of the withdrawn
Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations with the adopted
WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations. The complete
proof and theorem signature are otherwise verbatim.

The proof obtains nonnegative factor complexes and a geometric comparison from
picard_kunneth_cech_models, transports the factor equivalences through the direct
sum, applies tensor_kunneth_nat, then uses cycle representatives to establish the
external-cup generator formula. Both current dependency signatures fit this
assembly, including the degree cast. No new mathematical route or split is needed.
Lean Finder returned no replacement geometric theorem; Loogle confirmed the direct
sum transport API. Source searches found the existing algebraic Kunneth theorem,
but no duplicate geometric conclusion. Read the unit route and the source proof
in Stacks varieties-lemma-kunneth and equation-kunneth-on-cech. Empty schemes,
zero coefficients and degree zero introduce no extra hypotheses in the proof.

Change record: coord/changes/C7-picard-kunneth-qcoh-iso-restoration.md.

The corrected theorem compiles in 5.4 seconds. Compiling the archived original
reproduces unknown identifiers scalarCohomology and externalCup; Lean explicitly
requests the replacement public import. The initially missing published Cech-model
object was handled by checking its exact unchanged current source separately and
then compiling that source with the item in the supported sandbox compile set.
The temporary dependency source was removed and is not delivered.
An importer probe checks the parent's unchanged isomorphism clause by applying the
restored theorem; it compiles in 10.8 seconds. The axiom print contains propext,
Classical.choice, Quot.sound and sorryAx inherited from existing dependencies.
There are no new axioms or local holes.

## Proved and sorry left

The quarantined original has zero local sorry bodies. The restored module also
has zero. Holes closed: 0 of 0. Holes added: 0. Split off: 0.
AlgebraicGeometry.Scheme.Modules.picard_kunneth_iso_exists retains its complete
proof, attached to lem-sc-picard-kunneth-qcoh-iso-exists. This is a restoration and
import repair, not a newly closed hole. No sorry declaration remains in this packet.
Existing unfinished dependencies are not claimed proved by this repair.

## No longer needed

Removed direct import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations,
an empty withdrawn module, and replaced it with the actual adopted source module.
No mathematical node or module is pruned or withdrawn. Retained both declared
proof dependencies, lem-sc-picard-kunneth-cech-models and
lem-sc-qcoh-cech-total-tensor-nat-iso, and their private proof imports.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantine restoration assignment with zero local holes. Its archive
predates withdrawal of the Sheaf field-linear operations module. Restoring it
without correcting that public import would leave an unusable public statement.
The DAG's Lean attachment and argument remain correct and require no update.

The quarantined parent PicardKunnethQcoh still applies this theorem and cites its
node. Its absence from lean/ does not make this item unnecessary. The archive,
parent dependency and unit route are preserved. No statement or definition changes.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
