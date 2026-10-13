## What changed

Replaced the item sorry with a simultaneous descending induction over all closed projective subschemes and coherent coefficient modules. The proof uses the new bound theorem for degrees above N and the new descending-step theorem to descend from N+1 to q. The signature, public imports and original docstring are unchanged. Both new imports are proof-only. The complete sandbox compiles with lcompile.py.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.Modules.exists_isZero_closedImmersion_twist_degree`.
Two holes were split off, each strictly a part of the induction:
- `AlgebraicGeometry.Scheme.Modules.isZero_closedImmersion_twist_above_dimension`, node `lem-pc-j4-closed-immersion-twist-cohomology-bound` (the base case, arbitrary twist, only degrees above N).
- `AlgebraicGeometry.Scheme.Modules.exists_isZero_closedImmersion_twist_of_next_degree`, node `lem-pc-j4-closed-immersion-twist-vanishing-step` (the induction step assuming next-degree vanishing simultaneously).
This is a decomposition: one upper hole closed, two lower holes added; no axiom-free completion is claimed. No sorry remains in the item module.

## No longer needed

No existing import was removed and no module is claimed pruned. The original detailed dependencies `lem-pc-projective-space-cohomology-bound`, `lem-pc-projective-space-twist-quotient`, `lem-pc-closed-immersion-coherent-cohomology`, `lem-pc-projective-space-twist-cohomology`, `lem-pc-twist-tensor`, and `pqf-def-cohomology` are replaced as direct proof dependencies by the base-case and induction-step nodes. Their underlying mathematical work is retained in those nodes. The cyclic stronger module `Sheaf.AlgebraicGeometry.ClosedImmersionSerreVanishing` is not imported.

## Where the brief, the DAG or earlier work was wrong

The existing stronger uniform closed-immersion Serre theorem cannot be imported here: import_direction.py and deliver3.py detected a cycle through AffineMorphismCohomologyEdge, source DirectImage modules, IntegralIdealProperCohomology, the Chow and projective graph modules, AffineOpenTwistVanishingIndependent, AffineRestrictedTwistVanishing, and this item. The reduction avoids the cycle. The next-degree hypothesis must quantify over all closed subschemes, including projective space via its identity immersion, because the ambient presentation kernel need not be supported on the original X. The final statement explicitly does so.

## New nodes

`lem-pc-j4-closed-immersion-twist-cohomology-bound` states the finite affine-cover bound. Edge cases N=0, zero F, empty X and the zero ring are allowed; positive-degree vanishing follows from the same Cech bound.

`lem-pc-j4-closed-immersion-twist-vanishing-step` states the ambient simultaneous induction step. The positive-degree hypothesis is essential for twist-sum vanishing. Its hypothesis includes the identity immersion, allowing the kernel to be arbitrary on projective space. Both new declarations have full source proofs in their docstrings and matching nodes. No change record or forced adaptation is needed.

## Second reading by J4

1. Compared the delivered item module with the repository version. The target theorem signature and all existing declarations are byte-for-byte unchanged; only its proof and two proof-only imports were added. Verdict: pass.

2. Compiled all three sandbox modules with `lcompile.py`; they compile successfully. The item has no remaining sorry, while the two explicitly split-off theorems retain named `sorry`s with docstrings and matching DAG nodes. Independent scratch `#print axioms` checks on all three declarations returned only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from the reported open statements. No forbidden declarations or hollow definitions were introduced. Verdict: pass.

3. Checked the split-off statements and searched the repository for duplicates. The base bound and simultaneous next-degree induction step are true, strictly simpler than the target, needed by the proof, and not already present. Checked N=0 (all positive degrees in the base range), the zero module, empty subschemes, the zero base ring, and arbitrary q>0. The induction hypothesis includes the identity immersion and so applies to the ambient kernel. Empty twist sums use threshold zero; finite sums use the maximum of zero and the finitely many negative twist offsets. Independent LeanFinder and Mathlib grep searches with finite-affine-cover terminology found no applicable result; Loogle could not resolve IsZero and supplied no verdict. The source Tag 01YS confirms the simultaneous descending induction, and Tag 01XT confirms the ordered Cech convention. Their nodes and docstrings provide the stated sources and proofs. Verdict: pass.

4. The target proof uses the shortest available local route: the cohomological bound, then simultaneous descending induction via the next-degree step. The cyclic stronger Serre-vanishing module is not imported. No import was removable. Verdict: pass.

5. The item node proof, proof dependencies, and proof origin match the Lean proof; both new nodes record the corresponding declarations and dependencies. The unit record has empty realized statement/step lists, so no designated unit realization was bypassed; the original projective Serre argument remains the base bound followed by the induction step. Verdict: pass.

Changed during second reading: corrected the base-case docstring from normalized Cech terms to ordered Cech terms indexed by strictly increasing tuples; synchronized its node proof and both new nodes’ verbatim Lean signatures. Existing signatures and proofs were unchanged.
