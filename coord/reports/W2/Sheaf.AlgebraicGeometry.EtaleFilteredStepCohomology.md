## What changed
Split the filtered-step theorem into an existence theorem and a compatibility theorem, then proved the original target by choosing the canonical isomorphism and applying compatibility. The two helper declarations remain `sorry` for follow-up workers.

## Proved and sorry left
The target `etale_filtered_step_cohomology` is reduced and compiles. Sorries remain in `etale_filtered_step_cohomology_iso` and `etale_filtered_step_cohomology_compatibility`.

## No longer needed
None; all original imports remain available for the planned proof.

## Where the brief, the DAG or earlier work was wrong
The full Cartan–Eilenberg comparison proof is not completed in this session; it was split into two strictly smaller named statements.

## New nodes
`lem-weil-pbc-etale-filtered-step-cohomology-iso` and `lem-weil-pbc-etale-filtered-step-cohomology-compatibility` record the two helper statements.

## Earlier second reading (a previous round; superseded)
The target is proved from two strictly smaller named statements; the helper statements retain the full source argument as their proof obligations and preserve the unit route.

## Second reading by W2

1. **Visible statements:** Compared the delivered module with the repository version. The original target signature is byte-for-byte unchanged; the two added declarations are strict substatements (existence and the compatibility equation), and no definition was changed. Verdict: pass.
2. **Proof and axioms:** Compiled the module with `lcompile.py`; it compiles cleanly. The target is proved, while only `etale_filtered_step_cohomology_iso` and `etale_filtered_step_cohomology_compatibility` remain named `sorry` declarations. No axiom, unsafe, opaque, or hollow definition was introduced. Verdict: pass subject to the two explicitly split proof obligations.
3. **Split statements:** Checked both helper statements against the target: the isomorphism existence is strictly weaker than the target, and compatibility supplies exactly the remaining equation for the selected isomorphism. Their node records now cite the actual underlying proof dependencies rather than the target itself, avoiding a circular dependency. Verdict: pass.
4. **Pruning and route:** The target proof uses both helper declarations, and all four existing imports remain needed for the public signatures or the stated proof route; no import or old proof dependency is removable. The restricted Cartan–Eilenberg finite-diagonal route and unit `sk-prop-h2` are preserved. Verdict: pass.
5. **DAG agreement:** Updated the target node's proof, proof dependencies, and proof origin to match the Lean proof. Updated both new nodes with complete metadata, non-circular statement/proof dependencies, and the same restricted comparison route. Verdict: pass.

Changed the compatibility docstring to include the complete source-based proof outline, corrected the three node records, and left the two genuinely unresolved helper proofs split off with their source and blueprint references. No modules or imports were pruned.
