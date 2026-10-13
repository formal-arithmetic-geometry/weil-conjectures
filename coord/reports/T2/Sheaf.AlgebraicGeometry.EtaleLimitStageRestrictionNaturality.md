## What changed

Repaired the proposed proof of `AlgebraicGeometry.Etale.tailOpenCohomologyMapDegree_restriction`. The submitted three-line proof did not compile: `openCohomologyPullback_restriction` was not imported, and the concrete transitions still required coefficient naturality and comparison coherence. The delivered proof calculates directly with the actual stage maps, uses a proved private transported-composition helper, and proves the coefficient equality from naturality and the component associativity laws in `BaseChange.Pasting`.

Added proof-only imports `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial` and `WeilConjectures.SixFunctors.BaseChange.Pasting`. Both original public imports are required by the theorem's signature. Updated the theorem's proof explanation and its node's proof, proof_deps and proof_origin. No existing signature, definition, visibility or public import changed; no change record is required.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Etale.tailOpenCohomologyMapDegree_restriction` (node `lem-weil-pbc-etale-limit-stage-restriction-naturality`). Added zero holes. No sorry remains in the delivered module. The private `cohomologyMap_transported_comp` helper is fully proved. This is a proof, not a decomposition.

## No longer needed

The old proof dependency `lem-weil-pbc-open-cohomology-restriction-naturality` is not used by this direct argument. Its module `Sheaf.AlgebraicGeometry.EtaleCohomologyOpenRestrictionNaturality` was not imported by the original file and is not added. No existing import was removed; no claim of whole-library module pruning is made. The cohomology functoriality and inverse-image composition dependencies remain; direct-image composition coherence is recorded for the component associativity laws as in the existing nested-open naturality node.

## Where the brief, the DAG or earlier work was wrong

The first worker's report claimed that the three-line proof compiled and completed the argument; the second reader reproduced its unknown-identifier error and its unsolved goal. The original node's route described rewriting through inverse-image opens and the separate nested-open pullback lemma; the repaired direct square computation makes those intermediate transports unnecessary. No mathematical statement or unit route was changed.

## Second reading by T2

1. Compared the delivered module with the repository version. The existing theorem signature is byte for byte identical, including the arbitrary coefficient morphisms, degree, tail indices and elementwise equality. There are no changed definitions or public imports. The only added declaration is a private, fully proved composition helper. Verdict: interface preserved.
2. Read every proof step and locally compiled the complete repaired module without errors or warnings. The submitted proof failed compilation and was repaired. No sorry, axiom, unsafe, opaque, implemented_by or extern occurs in the delivered Lean. The axiom check and delivery preflight are recorded below. Verdict: genuine composition-and-coherence proof, zero new holes.
3. No statement was split off and no new node was introduced. The private helper is the same elementary transported-composition calculation already used in `EtaleCohomologyOpenRestrictionNaturality` and `TailOpenCohomologyLegNaturality`; it applies existing functoriality rather than assuming the result. Checked empty/equal opens, singleton/identity stages, zero coefficient maps and degree zero: the argument imposes no extra condition, cancellation is only of open inclusions, and coefficient naturality applies to arbitrary φ. Verdict: no duplicate open statement or circular reduction.
4. Searched the local library for restriction/pullback naturality and read the existing nested-open proof, tail-leg proof, concrete map definitions and `BaseChange.Pasting`. The direct calculation avoids transport to standard inverse-image opens and uses the already proved source component laws. Both public imports are needed for the signature; both new plain imports are used by the proof. The old restriction-naturality dependency is listed above. Read `dag/units/sk-thm-p1.json`, including `realized`: this item is below the unit's recorded statement and steps, and this local square calculation preserves their route. Verdict: shortest useful route found; no unit step bypassed.
5. Read the item's complete node and the declarations of its old proof dependencies. Updated proof, proof_deps and proof_origin to record the actual restricted square, transported composition, arbitrary-coefficient naturality and associativity cancellations. The statement, statement dependencies, unit and chapter are unchanged. Verdict: node and Lean agree.

Second reading changed the incomplete proof into the direct square computation, added the two proof-only imports and proved private helper, corrected the proof docstring and DAG route, and corrected this report. No split-off theorem or interface change.

Validation: `deliver3.py T2 Sheaf.AlgebraicGeometry.EtaleLimitStageRestrictionNaturality --no-push` printed OK: the complete module compiles and passes preflight, including the per-declaration axiom probe. Review class is CODEX because the proof record of the existing node changed.

Explicit scratch `#print axioms` verification of both the repaired theorem and the private composition helper completed through `lcompile.py` against the published build in 44.7 seconds. Both depend only on `propext`, `Classical.choice` and `Quot.sound`; neither depends on `sorryAx`. The separately compiled main module passed in 48.3 seconds, and the dry run passed its full declaration probe. Some local scratch reruns timed out; no failed optimization experiment was adopted.
