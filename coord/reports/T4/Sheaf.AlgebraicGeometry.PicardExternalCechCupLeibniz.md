## What changed

Replaced the supplied sandbox proof of
`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupBidegree_leibniz`
with the tested ordinary-Cech transport route. Its three specified bidegree maps,
coordinate hypotheses, universe, field, arbitrary families, modules, signs and degree
transports are unchanged. The statement is byte-identical to the supplied archived
signature. The assigned module and its coordinate-corollary module are absent from the
checkout after rollback, so this delivery restores those archived statements.

Added the fully proved module
`Sheaf.AlgebraicGeometry.PicardExternalCechCupTransport`. Its real construction
`picardCechScalarIso` composes the scalar and ordinary additive Cech identifications.
The lemmas `picardCechScalarIso_apply`, `picardCechScalarIso_d` and
`picardCechScalarIso_cast` give its coordinate, differential and degree-transport API.
`picardExternalCechCupBidegree_transport` identifies each prescribed external pairing
with the ordinary cup of the two refined factor cochains. Its private restriction
composition helper is proved directly by presheaf functoriality.

The main proof chooses the unique, already proved refinement cochain maps along the two
projections, uses transport in the three bidegrees, and applies the already proved
`cechCupCochain_leibniz` on the product scheme. The composite cochain maps' commutation
equations transport the two factor differentials. There is no new face-sum calculation.
The coordinate corollary retains its complete proof by evaluating the main equality.
All new imports used only by proofs are ordinary `import` lines.

Updated the main node's proof, proof_deps and proof_origin to match this argument, and
added the transport node. The coordinate node retains its evaluation proof and signature.
The change record is
`coord/changes/picard-external-cech-cup-leibniz-coordinate.md`.
No unrelated Paper module is included in the delivery.

Validation: all three delivered modules compile without warnings under lcompile.py,
individually within the 60-second limit (transport 19.7 s, main 24.0 s, corollary 2.7 s).
The axiom checks for all five public transport declarations, the main theorem and its
coordinate corollary report only `propext`, `Classical.choice`, `Quot.sound`.
The import-direction checks permit the ordinary cup and refinement imports.
The final dry run rebuilds an empty sandbox compilation cache, excluding compiled
artifacts retained from unrelated earlier work.

## Proved and sorry left

The assigned obligation
`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupBidegree_leibniz`
(node `lem-sc-picard-external-cech-cup-leibniz`) is proved with only the three permitted
axioms. This closes the original archived obligation and removes the supplied proof's
dependence on the open external differential-coordinate calculation.

The retained corollary
`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupBidegree_leibniz_coordinate`
(node `lem-sc-picard-external-cech-cup-leibniz-coordinate`) is also proved with only those
axioms; its proof was already complete in the supplied sandbox.

All four public theorems in the transport module are proved, and its isomorphism is a
real composition of existing isomorphisms. No delivered declaration contains sorry.
Holes added: zero. Split-offs left unproved: zero. The new transport node is fully proved.
Because the assigned module was withdrawn from the checkout, these figures describe the
restored archived obligations, not a claimed measured net change from the pinned ledger.

The existing
`AlgebraicGeometry.Scheme.Modules.picardExternalCechCupDegreeMaps_comm_ι`
(node `lem-sc-picard-external-cech-cup-differential-coordinate`) remains open in its own
module. It is no longer used by this proof. That module is held by another group in the
supplied checkout and is not changed here. The main theorem can now be used to finish its
summand calculation by expanding the tensor-total differential and tensor extensionality.

## No longer needed

Removed the proof-only import
`Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferentialCoordinate` from the supplied
main module, and removed node
`lem-sc-picard-external-cech-cup-differential-coordinate` from the main node's proof_deps.
The main proof no longer uses `picardExternalCechCupDegreeMaps_comm_ι`, tensor-total
inclusions, degree-map assembly or any face-calculation descendants of that route.

The proof also no longer uses `picardExternalCechCupBidegree_exists`: it works directly
with h, h₁ and h₂. The old proof dependency
`lem-sc-picard-external-cech-cup-bidegree` is removed from the main proof_deps but stays
in stmt_deps for the prescribed coordinate predicate. The bidegree module remains a public import because the unchanged
statement needs its coordinate predicate and coefficient definitions. Its existence
node is consequently not claimed as an entirely pruned module.

The main theorem does not import or use
`Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegreeLeibnizCoordinate` or node
`lem-sc-picard-external-cech-cup-leibniz-coordinate`; that restored module is retained as
a proved corollary importing the main theorem. No external Leibniz coordinate hole is
left. `PicardExternalCechModuleRepresentatives`, its cycle hypotheses, and the duplicate
n2 cup definitions from CechCupProductCore are not needed by the cochain transport proof.

No whole-library pruning count is asserted: DifferentialCoordinate is still imported by
`Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferential`, which uses its inclusion
compatibility theorem. Every import in each delivered module is used. No unit statement,
unit step or realized entry changes.

## Where the brief, the DAG or earlier work was wrong

The supplied sandbox's earlier reduction through the inclusion-level differential
identity still depended on sorry. The route note correctly identifies the shorter proof:
the ordinary cup Leibniz theorem becomes applicable after refining both factors to the
same product family and identifying scalar and ordinary additive cochains. The complete
transport interface is proved here, with no residual obligation handed to another group.

The archived modules are absent after rollback; this does not change the held theorem's
statement. Both restored signatures match the supplied archive exactly. The unrelated
ModuleCupNaiveDerivedCompatibility file from the old sandbox is excluded.

Read Stacks Tags [01FD](https://stacks.math.columbia.edu/tag/01FD),
[07MB](https://stacks.math.columbia.edu/tag/07MB) and its surrounding product construction,
and [0BED](https://stacks.math.columbia.edu/tag/0BED), equation-kunneth-on-cech.
The latter constructs the external map by the two refinements followed by the ordinary
cup, exactly the route used here. The geometric hypotheses for the cohomology isomorphism
are unnecessary for these cochain formulas. The Lean proof treats arbitrary families and
modules. Degree zero, empty families, zero modules and characteristic two need no new
hypotheses: the coordinate equalities and ordinary Leibniz theorem cover them.

The new transport result was checked against the existing private cycle conversion in
PicardExternalCechModuleRepresentatives and against the full blueprint by searches for
"external Cech cup" and "refinement cup"; neither blueprint search found a matching node.
LeanFinder found generic differentials, Loogle supplied restriction composition, and
Mathlib grep found no Cech cup transport theorem. LeanSearch returned HTTP 500 and is
recorded as unavailable. No false-statement dispute or forced adaptation is needed.

## New nodes

`lem-sc-picard-external-cech-cup-transport` records the fully proved equality between a
single external bidegree pairing and the ordinary cup of refined scalar cochains. It
has its source, complete coordinate proof, actual logged Mathlib searches, exact Lean
signature, chapter/unit and blueprint ancestry. Its module also supplies the real scalar
identification and the elementary conversion API used by the main proof. It adds no hole.

`lem-sc-picard-external-cech-cup-leibniz` restores the archived held node and records its
new route through transport, ordinary cup and refinement maps. Its statement is unchanged.

`lem-sc-picard-external-cech-cup-leibniz-coordinate` restores the archived coordinate
corollary node, whose existing complete proof evaluates the main theorem.

Change record: `coord/changes/picard-external-cech-cup-leibniz-coordinate.md`.

## Second reading by T4

1. **Signatures and visibility: pass.** All three delivered modules and their nodes
   are absent from the supplied repository after rollback; diff reports the missing
   counterparts, rather than a proof-only modification of existing source files.
   I reconstructed the two archived Lean files from the exact diff in
   `coord/repair-notes/Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz.json`.
   Both theorem signatures are byte-identical to that independent archive. The
   coordinate module is identical in its entirety. The main changes only its author
   line, proof docstring, proof-only import, elaboration options and proof body.
   All three node lean.statement strings occur verbatim in their modules. No target,
   existing definition, hypothesis, degree, sign, universe or visibility changes.

2. **Proofs, construction and axioms: pass.** Independently compiled all three modules
   in import order through lcompile.py: transport 18.3 s, main 21.4 s, coordinate 2.5 s,
   without errors or warnings. The seven public declarations (the scalar isomorphism,
   its three API theorems, transport, Leibniz and coordinate Leibniz) each print exactly
   propext, Classical.choice and Quot.sound. There are no sorry or prohibited commands
   in the delivered Lean. The scalar isomorphism is an explicit composition of proved
   isomorphisms. The two refinement maps come from the proved exists_unique theorem;
   their tuplewise coordinates determine them, and their commutation equations supply
   precisely the two transported differentials. No arbitrary witness of an unproved
   existence theorem is used.

3. **New statements and existing results: pass.** No unproved statement is split off.
   Read the full transport formula and its coordinate proof: the successive front/back
   restrictions compose to the direct restrictions in hh, using Functor.map_comp and
   the thin category of opens. At p=q=0 the two factors share the single vertex; empty
   index families have no tuples in these positive tuple lengths; zero coefficients
   and characteristic two require no cancellation or nonzero assumption. Searched
   independently with LeanFinder for external Alexander--Whitney pullback coordinates,
   Loogle for restriction composition and grep for Alexander/Whitney/refinement; no
   existing external transport statement was found. Repository rg finds the private
   scalarIso in PicardExternalCechModuleRepresentatives, which cannot be called here,
   and cechCup_refinement_naturality, which concerns one common scheme morphism and
   adds quasi-coherence and a coefficient identification, so it does not replace this
   two-projection formula. The ordinary cechCupCochain_leibniz is already used.

4. **Route and pruning: pass.** Read [Stacks 0BED](https://stacks.math.columbia.edu/tag/0BED),
   [01FD](https://stacks.math.columbia.edu/tag/01FD) and
   [07MB](https://stacks.math.columbia.edu/tag/07MB). The product-cover map in 0BED
   explicitly combines the two refinements with the ordinary cup; 01FD supplies the
   pullback/restriction components. The cochain part needs none of the geometric
   hypotheses used later for the Kunneth isomorphism. The main proof transports the
   existing ordinary Leibniz identity rather than introducing another face calculation.
   The public bidegree imports are required by the signatures, and the public refinement
   import is required by transport's gamma and IsCechRefinementMap hypotheses. Both
   other imports are proof-only. No redundant explicit import remains. Compared the
   old node proof_deps reconstructed from the repair diff: both the differential-
   coordinate dependency and use of bidegree existence are accounted for under
   No longer needed; the latter stays a statement dependency. The sk-prop-av-cube
   unit's general-cube argument and its realized fields are untouched (the supplied
   realized lists are empty). This subordinate cochain identity changes no unit step.

5. **Nodes and report: pass after metadata corrections.** Verified that each node's
   proof_deps is exactly the union of its proof-step uses and that all cited nodes
   exist. The main node describes the actual three-bidegree transport and ordinary
   Leibniz proof; the coordinate node describes evaluation, and the transport node
   describes the coordinate comparison and explicit scalar isomorphism. Its source,
   searches, ancestry, chapter/unit, created and exact Lean record are present. Added
   the five public transport declarations to its lean.declarations field. Corrected
   the restored nodes' old search verdicts that incorrectly said the abandoned
   tensor-total route was used; the search queries and results are preserved.

Changes in this reading: no Lean changes were needed. Expanded the pruning report,
corrected the two historical search verdicts, recorded all transport declarations,
and added this independent review and the baseline-collision diagnosis below.

The earlier return's combined-import failure remains a baseline defect outside these
three modules. A scratch file containing only `module` and imports of the unchanged
GlobalTensorPullbackMonoidalNormalization and ModuleCupNaiveDerivedCompatibility fails
before importing any delivered module, with duplicate declaration
`AlgebraicGeometry.Scheme.Modules.instCommRingCarrierObjOppositeOpensCarrierCarrierCommRingCatToRingedSpaceRingCatObjFunctorIsSheafGrothendieckTopologyModuleRingsOpTop_1`.
The broader former batch-import probe fails at that same second import. This delivery
therefore does not claim to repair those unrelated Paper modules or the batch probe.
It does supply the independent successful per-module axiom checks formerly missing
for the two Leibniz modules. The maintainer must repair the two baseline instance names
or isolate the batch probes; this failure cannot be attributed to the restored signatures.
