## What changed

Proved `AlgebraicGeometry.Scheme.Modules.cupCech_signed_axis_pairing` in
`lean/Sheaf/Paper/CechCupSignedAxisPairing.lean`, without changing its signature.
Added proof imports of `Sheaf.Paper.CupCechTotalCochainPairing` and
`import all Sheaf.Paper.CechCupProduct`. The latter reuses its already-proved
private generic bilinear quotient descent and elementary cycle/boundary helpers.
The existing total cochain morphism supplies the signed Alexander--Whitney
construction and both cochain axis equations. New proved private helpers establish
tensor Leibniz, cycle preservation, boundary preservation in both variables,
and naturality of the concrete cycle kernel and cycle class maps. The final proof
identifies all six given axis maps componentwise and applies bilinear descent.
Updated the item's DAG proof, proof dependencies and proof origin to this route.
All definitions use explicit linear maps; no existence witness is used to define data.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.cupCech_signed_axis_pairing`
(node `lem-sc-cech-cup-signed-axis-pairing`), the item's sole original sorry.
Added: none. Remaining in the delivered module: none.
The existing theorem `exists_cupCech_total_cochain_pairing` and its imported
construction dependencies supply the cochain morphism; their own reachable holes
are existing downstream work, not newly introduced statements.
This is a proof from existing declarations, not a new-hole decomposition.
The private boundary proofs separately handle degree zero, so no negative primitive
or nonempty-cover assumption is used. Empty families and zero inputs are allowed.

## No longer needed

No imports removed, and no existing modules or nodes pruned: the original public
imports are still needed by the unchanged signature. The signed component calculation
is supplied by the already-stated total cochain morphism rather than duplicated in
new modules. The original three definition nodes remain used. No new nodes.

## Where the brief, the DAG or earlier work was wrong

The item DAG planned direct construction and descent but did not cite the existing
`lem-sc-cup-cech-total-cochain-pairing`, which now supplies the cochain morphism
with both axis formulas. Its coefficient formula uses `n2CechCupCochain`; this
is definitionally the same tuple formula as `cechCupCochain`, so no interface
change or adaptation is necessary. The unit `sk-prop-av-cube` has no realized
statement or step at this node; the cube/Kunneth route is preserved.

Searches: LeanFinder on bilinear complex pairings returned hom-complex results,
Loogle on `Submodule.liftQ` returned quotient APIs, and the upstream grep search
found no applicable tensor homology pairing. Local DAG/source search found the
existing total cochain morphism and the proved private quotient descent helper.

## Second reading by M2

1. Interface: PASS. Compared the sole delivered module against the repository
   with diff and checked the existing theorem signature byte for byte. It is
   unchanged; no existing definition or other public declaration changed. The
   node changes are confined to proof, proof_deps and proof_origin.
2. Proof: PASS. Read every new private construction and proof, including the
   tensor differential signs, degree transports, both boundary cases and cycle
   class naturality. The module compiles locally without warnings. There are
   no sorries or prohibited declarations in the delivered module and no data
   selected from an existence theorem in a definition. The cochain morphism is
   destructured inside the theorem proof, not used to define an arbitrary
   public object. Its existing dependency exists_cupCech_total_cochain_map is
   still open; this delivery therefore closes the local hole, not the entire
   axiom closure. A scratch-copy #print axioms reports exactly propext,
   Classical.choice, Quot.sound and sorryAx from existing dependencies. The
   delivery tool also probes every added declaration.
3. Split statements: PASS, none added. All new helper statements are proved.
   Checked p=0 and q=0: incoming boundaries vanish; positive right boundaries
   use (-1)^p twice, whose square is one. No cover nonemptiness, inverse
   comparison, field hypothesis or nonzero input is assumed.
4. Route and pruning: PASS. Independently searched LeanFinder for cochain
   tensor products inducing bilinear homology maps and searched the local
   library for homology pairings. TensorHomologyPairing handles integer-indexed
   complexes, not the natural-number complexes here; derived pairings require
   different interfaces. The existing total cochain theorem plus the proved
   CechCupProduct quotient helper is a direct route. Both original public
   imports provide signature data; both added imports serve the proof only.
   The import-all line is needed for the private quotient and cycle helpers.
   All three old proof dependencies remain used, so none is omitted from
   No longer needed. The cube unit has empty realized statement/step lists;
   its prescribed route is preserved.
5. DAG: PASS. Checked that the steps describe the actual tensor insertion,
   Leibniz, quotient descent and axis proof, and that proof_deps equals the
   union of step uses. The added dependency names the existing total cochain
   theorem. No new node or statement-change record is required.

Changes by this reader: added this review and clarified the existing open
cochain-map dependency. No Lean or DAG repair was needed.

## New nodes

Restored `lem-sc-cech-cup-signed-axis-pairing`, the assigned existing item node
which the newer fetched baseline removed. Its statement and Lean signature
are those reviewed at session start; restoration updates creation/delivery
metadata to M2. This is not a split-off statement and adds no hole.

## Restoration after baseline update

The first dry run fetched a newer baseline without the assigned module and
node. The reader added coord/changes/cech-cup-signed-axis-restoration-M2.md,
updated the restored node's delivery metadata, and removed historical review
stamps so the new landing records its own review. The five mathematical
verdicts above remain valid. No current Lean source imports the absent module;
no consumer adaptation is required. No Lean code was changed by the reader.
