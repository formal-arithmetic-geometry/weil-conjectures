## What changed

Proved `AlgebraicGeometry.affine_finite_free_model_bounded` with bounds `-(r : ℤ)` and `0`, using Mathlib's extension-by-zero API and preservation of zero objects. The existing declaration signature, public import, and all definitions are unchanged.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.affine_finite_free_model_bounded` (node `lem-affine-finite-free-model-bounded`), one of one original holes. Holes added: none. No sorry remains in the delivered module. This is a proof, not a decomposition. The first worker's proposed `AlgebraicGeometry.affine_finite_free_model_bounded_lower` was removed after its argument was proved inline.

## No longer needed

None of the old proof dependencies or imports is pruned: `def-affine-finite-free-model-complex` is still used. The proposed new helper node `lem-affine-finite-free-model-bounded-lower` is removed from the delivery.

## Where the brief, the DAG or earlier work was wrong

The first worker treated the lower-degree calculation as substantial unresolved reindexing. Mathlib's `HomologicalComplex.extendXIso` makes it a short direct argument. Its proposed helper docstring lacked a complete proof, and its statement dependencies referred back to the item; removing the helper avoids these faults. The existing node's proof has been updated to record both branches precisely.

## Second reading by Q2

1. Compared the full delivered module with the repository version. The original theorem signature is byte for byte unchanged, including all scheme, affine-open, chain-complex, bound and termwise-zero hypotheses and the existential bounded-support conclusion. No definitions, visibility or public imports changed; no change record is needed.
2. Compiled the first worker's module and the repaired module through lcompile.py. The repaired file has no sorry or forbidden declarations; the separate scratch `#print axioms` check reports exactly `propext`, `Classical.choice`, and `Quot.sound`. The proof constructs explicit integer bounds and uses only termwise zero preservation and extension isomorphisms.
3. No split-off statement remains. Read the proposed lower-support node and checked the argument: n < -r implies n < 0 and r < (-n).toNat, with embeddingDownNat.f (-n).toNat = n. This includes r = 0, the zero complex and empty affine opens; boundary degrees -r and 0 are correctly excluded. Searched lean/Sheaf and upstream for bounded support and embeddingDownNat, and read Mathlib Algebra/Homology/Embedding/Extend.lean: extendXIso gives exactly the required term identification. No new lemma or node is needed.
4. The proof proceeds directly from the explicit model and Mathlib. The sole import is required by the statement. The original proof_deps consists only of def-affine-finite-free-model-complex, which remains used; therefore No longer needed is complete. Read dag/units/sk-thm-picard-duality.json: its realized statement and step arrays are empty, and this termwise calculation changes no unit route.
5. Read the existing item node and proposed helper node against the Lean. Updated the item's proof and proof_origin to describe the actual lower and upper calculations; proof_deps stays exactly the explicit model definition. Removed the helper node together with the helper declaration. No new nodes or statement changes remain.

Changes made in this reading: closed the lower-support hole inline, removed its new theorem and node, shared the model unfolding and zero preservation between branches, restored exact signature whitespace, and corrected the report from decomposition to a complete proof.
