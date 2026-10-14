## What changed

Completed `AlgebraicGeometry.Scheme.Modules.picardExternalCechCupDegreeMaps_comm_ι` in
`Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferentialCoordinate`. The proof substitutes the
sum index, recovers the bidegree component, expands `HomologicalComplex.mapBifunctor.d_eq`,
uses the two coprojection and adjacent differential formulas, and reduces the map equality to
pure tensors. The natural-index signs are then discharged by the proved pure-tensor Leibniz
identity.

Added the proof-only module
`Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz`, which proves that identity by transporting
three adjacent external bidegree maps to ordinary Cech cup cochains. Added
`Sheaf.AlgebraicGeometry.PicardExternalCechCupTransport`, which supplies the scalar-to-ordinary
Cech comparison, coordinate transport, differential compatibility, and equal-degree cast
lemmas. All delivered declarations compile with only `propext`, `Classical.choice`, and
`Quot.sound` in their axiom lists.

## Proved and sorry left

The original hole
`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupDegreeMaps_comm_ι` is closed. The two
new modules contain complete proofs and add no `sorry`; there are no sorries left in this
delivery.

## No longer needed

The item now imports only the public bidegree module and the proof-only
`Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz`. Its former direct proof imports
`Sheaf.AlgebraicGeometry.PicardExternalRightCechModels`,
`Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`, and `Sheaf.Paper.CechCupProduct` were
redundant because the bidegree module already publicly imports the declarations needed by the
item's definitions and statement. The temporary route module `Route.PairingTransport` is not
delivered; its conversion lemmas were promoted into the project transport module.

No unit-level route step is bypassed. The assembly uses the new pure-tensor node, and that node
uses the existing bidegree, right Cech model, refinement-map, and ordinary cup declarations
through the transport node.

## Where the brief, the DAG or earlier work was wrong

Earlier deliveries split the tensor-total assembly from a pure-tensor Leibniz statement but left
the latter as a `sorry`. The tested route closes that lower statement by identifying scalar and
ordinary Cech complexes and applying the existing ordinary cup Leibniz theorem. The assembly
therefore needs no coordinate-by-coordinate expansion or canonical-degree helper. The route
module used for testing was an external scratch module; its conversion declarations are
represented here by the project-namespaced transport module so that no unavailable `Route.*`
import remains.

## New nodes

`lem-sc-picard-external-cech-cup-transport` records the scalar/ordinary Cech comparison and the
transport of an external bidegree pairing to the ordinary cup after the two projection
refinements. Its Lean declaration is
`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupBidegree_transport` in
`lean/Sheaf/AlgebraicGeometry/PicardExternalCechCupTransport.lean`.

The import reduction is recorded in
`coord/changes/picard-external-cech-cup-differential-coordinate-proof-imports.md`.

`lem-sc-picard-external-cech-cup-leibniz` records the signed pure-tensor Leibniz identity for
three adjacent bidegrees. Its Lean declaration is
`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupBidegree_leibniz` in
`lean/Sheaf/AlgebraicGeometry/PicardExternalCechCupLeibniz.lean`; it combines the transport node
with the existing ordinary Cech cup product node.

## Review by N4

I compared the delivered assembly theorem with the baseline signature and checked that its
public bidegree import remains unchanged while all added imports are proof-only or new modules.
I compiled the three delivered modules in dependency order and checked their axiom prints. The
transport statement quantifies arbitrary families and cochains, the Leibniz statement uses only
three adjacent maps, and the assembly preserves the required tensor-total inclusion and degree
casts. The new nodes have matching Lean records, source descriptions, blueprint provenance,
and proof dependencies; no theorem is a restatement of the upper target and no unit step is
bypassed.

## Second reading by N4

1. **Signature preservation.** I compared the delivered coordinate module against the repository baseline. Existing declarations and definitions retain byte-for-byte signatures; only the proof and proof-only imports changed. The two added modules are new declarations recorded by matching DAG nodes.

2. **Proof and axioms.** I compiled Transport, Leibniz, and DifferentialCoordinate with `lcompile.py --all`. All compile without errors or warnings. The target theorem prints only `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition occurs.

3. **New statements.** The transport theorem states the scalar-to-ordinary Cech coordinate identity for arbitrary families and cochains; the Leibniz theorem states only the three adjacent pure-tensor bidegrees needed by the assembly. Both are strictly lower than the target, have source/docstring proofs, and their DAG nodes record the declarations and dependencies. I found no existing Mathlib or library theorem duplicating either result.

4. **Pruning and route.** The coordinate module removes redundant proof-only imports and adds the Leibniz module. The new modules use the existing bidegree, refinement, and ordinary Cech cup declarations. The tensor-total assembly still follows the unit route through the bidegree coordinate calculation; no unit-level step is bypassed. The removed imports are listed under `## No longer needed` and the change record.

5. **DAG and delivery metadata.** The target node proof and `proof_deps` match the Lean route, and both new nodes include source, proof, searches, Lean declarations, chapter, and unit metadata. The delivery dry run reaches the static preflight; its only initial report issue was this required second-reading heading, now supplied.

I changed the report by adding this required second-reading record. No Lean statement or proof was changed during this reading.
