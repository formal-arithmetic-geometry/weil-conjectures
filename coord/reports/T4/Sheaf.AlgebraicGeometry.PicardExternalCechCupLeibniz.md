## What changed

Repaired return A3 from reviewer X-1da79. Restored
lean/Sheaf/Paper/ModuleCupNaiveDerivedCompatibility.lean byte for byte from the repository
base, so it contributes no delivery diff. Deleted
coord/changes/T4-naive-derived-cup-instance-names.md and removed its associated repair and
authorization claims from this report and the remaining change record.

The original ModuleCupNaiveDerivedCompatibility compiles against the delivered dependencies. Its independent instance-name collision repair is excluded from this delivery.

Kept both Leibniz modules and their matching DAG nodes unchanged from the returned sandbox:
Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz and
Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegreeLeibnizCoordinate. Their signatures and
proof bodies remain unchanged. The remaining change record is
coord/changes/picard-external-cech-cup-leibniz-coordinate.md.

Validation: lcompile.py --all compiled the retained main theorem (5.7 s), the original
Paper module (50.4 s), and the coordinate corollary (3.5 s), with no errors or warnings.
SHA-256 comparisons confirm both Leibniz modules and both nodes are unchanged. Each node
records its Lean signature verbatim and its proof dependencies match its proof steps.

Removed the previous second-reading section because it certified the excluded adaptation.
The next independent reader supplies the second reading for this repaired delivery.

## Proved and sorry left

The assigned theorem
AlgebraicGeometry.Scheme.Modules.picardExternalCechCupBidegree_leibniz
(node lem-sc-picard-external-cech-cup-leibniz) has a complete proof from the existing
inclusion-level differential compatibility theorem. It compares bidegree maps through
coordinate injectivity, expands the tensor-total differential, evaluates on a pure tensor,
and substitutes the three specified maps.

The coordinate corollary
AlgebraicGeometry.Scheme.Modules.picardExternalCechCupBidegree_leibniz_coordinate
(node lem-sc-picard-external-cech-cup-leibniz-coordinate) has a complete proof by evaluating
the assigned theorem under the target Cech coordinate equivalence.

Neither Leibniz module contains a sorry. This A3 repair changes no theorem proof and closes
no additional holes. Holes added: none. Split-offs added: none. Relative to the earlier H3
reduction, the coordinate theorem's hole is closed and the main theorem remains proved.

The unchanged dependency
AlgebraicGeometry.Scheme.Modules.picardExternalCechCupDegreeMaps_comm_ι
(node lem-sc-picard-external-cech-cup-differential-coordinate) still has a sorry in
Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferentialCoordinate. The retained proof
uses it; this delivery does not claim an axiom-free closure or net progress in the targets'
import closure. It requires the construction-specific signed differential calculation
for the existing external Cech bidegree maps.

The chosen bidegree maps are determined on pure tensors by their prescribed coordinates.
Coordinate-equivalence injectivity identifies those values with the specified maps. No
arbitrary data from an unproved mere existence theorem is introduced.

## No longer needed

No import is removed by this A3 repair and no module is newly pruned.

Relative to the earlier H3 route, the main theorem no longer imports or uses
Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegreeLeibnizCoordinate
or node lem-sc-picard-external-cech-cup-leibniz-coordinate. The coordinate module is retained
as a proved corollary of the main theorem, so it is not claimed as a pruned module.
The existing differential-coordinate theorem remains necessary.

The restored ModuleCupNaiveDerivedCompatibility and its independent instance-name repair
are excluded from the delivery diff. No unit statement or proof step changes; both Leibniz
nodes remain in sk-prop-av-cube.

## Where the brief, the DAG or earlier work was wrong

The previous delivery incorrectly treated the independent Paper instance-name collision
repair as a required adaptation. Reviewer X-1da79 compiled the original compatibility
module against the delivered overlay without errors or warnings (37.9 s); the collision
did not result from this delivery's changes. Return A3 is repaired by excluding that edit
and deleting its change record, while retaining the two Leibniz modules and nodes.

The original ModuleCupNaiveDerivedCompatibility compiles against the delivered dependencies. Its independent instance-name collision repair is excluded from this delivery.

The main theorem's proof is an inclusion-level differential reduction, not an independent
face calculation. Its docstring and node already describe that actual argument. The
coordinate corollary follows from the main theorem, so their proof imports are acyclic.
Degree zero, empty index families, zero coefficients and characteristic two require no
additional hypotheses in either retained proof.

## New nodes

lem-sc-picard-external-cech-cup-leibniz: retained archived node for the assigned theorem.
Its proof dependencies are bidegree existence and the existing inclusion-level
differential-coordinate theorem.

lem-sc-picard-external-cech-cup-leibniz-coordinate: retained archived node for the coordinate
corollary. Its sole proof dependency is the assigned Leibniz theorem.

Both nodes were already present in the returned sandbox and are preserved byte for byte.
No node or mathematical split is added in this A3 repair. The original restoration change
record remains at coord/changes/picard-external-cech-cup-leibniz-coordinate.md; the unrelated
Paper change record has been deleted.

## Second reading by T4

1. Visible declarations: PASS. Both restored Leibniz modules are absent from the
   supplied repository, as the return and change record state. I reconstructed
   their old source from the archived diff in
   coord/repair-notes/Sheaf.AlgebraicGeometry.PicardExternalCechCupLeibniz.json.
   Both theorem signatures are byte-identical to that archive, including the
   field and universe parameters, arbitrary open families, three specified maps,
   their coordinate hypotheses, both transports and the signed conclusion.
   The coordinate module is entirely identical to its archived source; the main
   module differs only in its documented proof docstring. The Paper module is
   byte-identical to the repository. The removed Paper change record is absent.
   No target statement, definition, instance or existing interface changes.

2. Proof and axioms: PASS, with the disclosed open dependency. I read the main
   proof line by line: heq follows by coordinate-equivalence injectivity from
   hl and hm; the inclusion theorem supplies hc; the two total differential
   inclusion formulas produce the transported first term and signed second
   term; evaluation and tensorHom_tmul give hv; the three heq substitutions
   produce exactly the conclusion. The coordinate theorem is congrArg of that
   conclusion. Compilation used a freshly rebuilt .lbuild after moving the old
   overlay into scratchpad/second-reading/previous-lbuild, avoiding stale Paper
   normalization artifacts. Both restored theorems' #print axioms in the scratch
   AxiomChecks module returned exactly propext, Classical.choice, Quot.sound and
   sorryAx. Neither delivered Leibniz module has a textual sorry, forbidden
   declaration, or definition. The chosen family is from the already proved
   bidegree existence theorem; heq determines every pure-tensor value, and tensor
   extensionality determines the linear maps. It supplies no arbitrary data.

3. Split statements and small cases: PASS. No new sorry or split-off is added.
   Both restored nodes state the two Lean assertions with every parameter and
   hypothesis, rather than a weakened special case. At p=q=0 the total signs
   are both +1 and both transports lead to degree one; when one index family
   is empty the coordinate domain is empty and injectivity still applies.
   Zero modules give zero values; characteristic two preserves the integer
   scalar action and the same algebraic identities. I independently searched
   with msearch.py leanfinder for "Cech cohomology external product coboundary
   derivation rule" and loogle for HomologicalComplex.mapBifunctor.d_eq, and
   searched lean/Sheaf, lean/WeilConjectures and Mathlib with rg. LeanFinder
   returned group/continuous-cohomology differentials, not this assertion;
   Loogle found the total-differential formula used here. I inspected
   cechCupCochain_leibniz and moduleCup_awSummand_leibniz: the former concerns
   coefficients on one scheme and one open family, and the latter concerns
   cosimplicial sheaf complexes. Neither directly identifies the scalar external
   bidegree maps in this statement. No missing elementary proof was split off.

4. Route and pruning: PASS. The main proof uses the existing construction-specific
   picardExternalCechCupDegreeMaps_comm_ι, not a replacement theorem left sorry
   by this delivery. Both imports of each module are used: Bidegree supplies the
   public statement's objects and predicate; DifferentialCoordinate and Leibniz
   respectively supply proof-only declarations and are plain imports. There is
   no import cycle. The abandoned H3 coordinate dependency is fully listed under
   No longer needed; its module is retained as a proved corollary, not falsely
   counted as pruned. I read sk-prop-av-cube's statement, step and realized record:
   these restored nodes are below its unit step, and no unit route or realized
   entry is changed. Stacks 07MB and its surrounding Cech-complex product formula,
   and 0BED's equation-kunneth-on-cech, were read at the official Stacks site.
   The stronger covering and quasi-coherence assumptions used to compute
   cohomology there are unnecessary for this cochain equality.

5. Nodes: PASS. Both lean.statement fields are byte-identical to the corresponding
   theorem signature. Each proof_deps is exactly the union of its steps' uses;
   the main node records bidegree existence and inclusion differential
   compatibility, and the coordinate node records evaluation of Leibniz.
   Sources, proof_origin, self-contained statements, chapter/unit, created and
   blueprint records are present. The recorded searches match searches.jsonl.
   These nodes restore archived declarations and add no holed theorem.

Second-reading changes: added this independent review and its scratch evidence;
no Lean proof, signature, import, node or change record needed repair. The A3
return is satisfied point by point: the original Paper file is restored exactly,
its separate change record is removed, its repair/authorization claims are
excluded, and both Leibniz modules and matching nodes are retained. This repair
closes no additional hole relative to the returned proofs, adds none, and prunes
none; the imported differential calculation remains open.
