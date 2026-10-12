## What changed

Proved `CategoryTheory.InjectiveResolution.exists_horseshoe_resolutions` by choosing the canonical injective resolutions `InjectiveResolution.of` for the two outer objects and applying the existing theorem `exists_horseshoe_prescribed_resolutions`. Added the proof-only import `Sheaf.CategoryTheory.Abelian.HorseshoePrescribedResolutions`. Updated the node proof dependencies and proof origin to record this route.

## Proved and sorry left

The module's sole theorem is proved. No `sorry` remains in the delivered module, and no new statements were added.

## No longer needed

The original proof dependencies `def-sp-abelian` and `def-sp-injective-resolutions` are not used directly by this proof; the prescribed-resolution horseshoe theorem subsumes them. No public imports were removed.

## Where the brief, the DAG or earlier work was wrong

The planned multi-step constructive proof is unnecessary because the library already contains the stronger prescribed-endpoint horseshoe theorem. The target statement is unchanged.

## Second reading by F1

1. Compared the delivered module with the repository version: the theorem statement is byte-for-byte unchanged; only the proof and proof-only import differ. Verdict: pass.
2. Compiled the module successfully. There are no `sorry`s in the delivered module, and no forbidden declarations; the temporary axiom check reports only the open imported prescribed-resolution theorem in addition to permitted axioms. Verdict: pass.
3. No statements were split off or added. The existing theorem is applied unchanged, and its prescribed-resolution witness is exactly strong enough. Verdict: pass.
4. The proof uses the shorter existing prescribed-endpoint horseshoe theorem, with `InjectiveResolution.of` for both outer terms. The proof-only import is minimal for this route; the former abelian and injective-resolution proof dependencies are pruned in the node. Verdict: pass.
5. The node proof, `proof_deps`, and `proof_origin` match the Lean proof; the unit route remains represented by the existing prescribed-resolution node. Verdict: pass.

Changed the report only by recording this second reading. No repair to the Lean proof was needed.
