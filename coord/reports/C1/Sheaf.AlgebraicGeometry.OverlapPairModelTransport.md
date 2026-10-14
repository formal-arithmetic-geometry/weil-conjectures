## What changed

Proved `AlgebraicGeometry.overlap_pair_square_of_model_recovery` in
`Sheaf.AlgebraicGeometry.OverlapPairModelTransport`, with its statement unchanged.
Constructed the map from the iterated overlap to the fixed limit model, proved both chart
projection identities and the base-change square, and applied the two existing restriction
lemmas through the proved private helper `overlap_model_restrictions_compose`.

Added the real constructions `overlapModelStageComparisonFst` and
`overlapModelStageComparisonSnd`; the pair-map definition uses these instead of identical
local let-bindings. This prevents expansion of the chart isomorphisms during specialization.
No existing signature, visibility, or public import changes. The node's proof record follows
the implemented argument. Change record:
`coord/changes/C1-overlap-pair-chart-constructions.md`.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.overlap_pair_square_of_model_recovery`
(node `lem-pc-overlap-pair-model-transport`). Added 0 holes; no `sorry` remains in the delivered
module, including its private helper and all definitions. This is a proof from existing
statements, not a decomposition into new holes.

The proof uses the already stated `AlgebraicGeometry.overlap_stage_model_restriction`
(node `lem-pc-overlap-stage-model-restriction`) and
`AlgebraicGeometry.overlap_conjugate_restriction`
(node `lem-pc-overlap-conjugate-restriction`). Their existing proof obligations remain outside
this delivery. Single-module compilation passed without warnings in 23.1 seconds. The original
`Sheaf.AlgebraicGeometry.FinitePresentationOverlapPairSingleStage` also compiled unchanged
against the delivered module in 47.7 seconds, without warnings; it is not part of the delivery.

## No longer needed

No original imports, nodes, or modules are pruned. The proof uses all three original imports.
Removed the earlier sandbox-only duplicate declaration and node
`overlap_pair_square_of_model_recovery_for_alpha` /
`lem-pc-overlap-pair-model-transport-alpha`; neither is part of the delivered library route.

## Where the brief, the DAG or earlier work was wrong

The earlier fixed-alpha lemma quantified alpha and its recovery hypothesis with exactly the
parent theorem's conclusion. It was a restatement, not a smaller argument. The earlier report
also claimed a second reading; that obsolete section is removed for the independent reader.

The mathematical DAG plan fits the original statement. A direct specialization caused
expensive expansion of concrete chart comparison terms. Named real chart constructions and
a proved generic composition helper resolve that compilation issue without changing the
argument or adding a hole. The inherited sandbox also contained a large stale source-library
snapshot; it is archived outside `lean/`, so it cannot enter this delivery as unrelated files.

## Second reading by C1

Independent second reader, 2026-10-14; I did not write the delivered proof.

1. **Visible declarations: PASS.** Read the complete diff against the repository and
   checked the declaration table: all existing signatures and visibility are unchanged,
   byte for byte. The only existing bodies changed are `overlapPairMapOfModel` and
   `overlap_pair_square_of_model_recovery`. The former replaces two local constructions
   by definitions with exactly those bodies; the supplied change record records this.
   Searched both library roots for users: the single-stage module is the only external
   direct user. Independently compiled its unchanged source against the delivered
   overlay without warnings (44.3 s). No target statement or unrelated module is edited.
2. **Proof and data: PASS.** Compiled the delivered module independently without warnings
   (20.4 s). A scratch-copy axiom probe compiled without warnings (17.9 s): the recovery
   theorem uses only `propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx`;
   both new chart constructors and the changed pair-map definition use only the three
   allowed axioms. Text inspection found no local `sorry` or forbidden declaration.
   Read every geometric lift and projection proof and the private helper's applications
   of the two restriction theorems. No existence witness is chosen by this delivery.
   The inherited adjunction choice is pinned by its unit, and its source theorem is
   already proved. Definitions therefore contain actual constructions, not holed data.
3. **Split statements: PASS, none added.** There are no new open statements or nodes.
   The private composition helper is proved from the two existing restriction theorems,
   rather than postulating the item under another name. Read those statements and their
   word proofs: stage transport and conjugated-transition restriction are distinct parts
   of the argument. Empty overlaps, zero modules, repeated charts and identity stage maps
   do not invalidate the projection or cancellation calculations; no extra finiteness,
   directedness, nonemptiness or limit hypothesis is introduced.
4. **Route and pruning: PASS.** The proof uses Mathlib pullback uniqueness and lift
   projection identities, then the existing two restriction lemmas. Independent Loogle
   search confirmed `CategoryTheory.Limits.pullback.hom_ext`; library searches found
   no proved fixed-model recovery replacement. All three imports are needed:
   conjugate constructors and tensor composition appear in public definitions/signatures,
   while stage restriction is a plain proof-only import. Every original proof dependency
   remains used, so the report's pruning list is complete. The unit
   `sk-thm-picard-semicon` and its inherited `realized` record are untouched; this changes
   only the node-level restriction calculation and bypasses no unit step.
5. **DAG: PASS.** Compared the delivered JSON with the repository: only `proof` and
   `proof_origin` differ. The geometric construction, named comparisons and proved generic
   composition helper agree with the code; the unchanged `proof_deps` is the union of
   the step uses. The node's statement, Lean statement, chapter and unit are unchanged.

Second reading changed only this report, adding the independent verdict and validation.
No Lean or node repair was needed. Closed 1 original hole and added 0 holes; the two
existing imported restriction obligations remain open outside this delivery.
