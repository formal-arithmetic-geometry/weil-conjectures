## What changed

Reviewed `Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling`; repaired the placement of an added module-documentation sentence. The two declarations are fully proved: the witness theorem constructs the locally surjective presheaf cover and verifies the Ext vanishing equation, and the final theorem applies it directly. The module compiles cleanly.

## Proved and sorry left

Proved `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness` and `CategoryTheory.Sheaf.exists_presheaf_ext_local_killing`. No `sorry` remains. Both proofs are already present in the repository baseline: holes closed by this delivery: none; holes added: none. This is verification, not new proof progress.

## No longer needed

No imports or proof-dependency nodes were removed; the witness uses `lem-sc-ext-epi-effacement` through `Ext.exists_epi_comp_eq_zero` and the local lifting construction; the final theorem uses `lem-sc-presheaf-free-ext-local-killing-witness`.

## Where the brief, the DAG or earlier work was wrong

The item was already fully proved in the repository baseline. The sandbox only added a documentation sentence in the middle of another sentence; its placement was repaired. No new mathematical progress is claimed.

## Earlier second reading (a previous round; superseded)

The declarations and DAG statements were checked against the source module; both proofs compile and no statement or hypothesis was changed.

## Second reading by H1

1. Compared the only delivered module with the repository using a file diff. Every existing declaration, signature, definition, visibility, import and proof is unchanged; only one module-documentation sentence was added and repositioned. No change record is needed. Verdict: pass.
2. Compiled the module locally without errors or warnings. Scanned for forbidden declarations and sorry: none. A scratch copy of the delivered source with #print axioms for both public theorems reports only propext, Classical.choice and Quot.sound. Reviewed the image subsheaf, factorization, explicit generator-pair presheaf, free lifting and Ext composition. No data is chosen from an unproved existence theorem. Verdict: pass.
3. No statements or holes are split off by this delivery; both existing public theorems are proved. The existing witness restates the conclusion but has a real proof, so it does not relocate a hole. The construction covers empty presheaves and q=1; q=0 is properly excluded. Verdict: pass.
4. Read top-down from the final theorem through its witness and helpers. Searched Mathlib and both library roots for epi/local-surjectivity and Ext effacement alternatives. Mathlib Sites.EpiMono.isLocallySurjective_iff_epi' requires additional WEqualsLocallyBijective structure, unlike the small-value-universe image argument here; upstream applications enlarge the value universe. The three imports serve the signatures or the actual proof; the proof-only ExtEpiEffacement import is plain import. No old proof dependency was removed. The unit sk-prop-cd realized fields and route are unchanged, with no unit step bypassed. Verdict: pass.
5. Read both corresponding DAG nodes and the effacement dependency: the final node applies the witness, and the witness node records effacement, the local image subsheaf, explicit pair construction, free/sheafification lift and Ext associativity. proof_deps and proof_origin agree with the unchanged Lean proof. No node edits or new nodes are required. Verdict: pass.

Changed only the placement of the module-documentation sentence and corrected the report to distinguish verification of existing proofs from newly closed holes.
