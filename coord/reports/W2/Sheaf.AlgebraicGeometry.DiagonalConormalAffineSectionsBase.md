## What changed
Added a proof-only decomposition module with two named intermediate theorems and used it to reduce the target to the canonical normalized derivation and transport by uniqueness. The two intermediate theorem proofs remain sorry because the affine geometric calculation and its uniqueness require substantial theory.

## Proved and sorry left
The target `AlgebraicGeometry.exists_diagonalConormal_affine_sections_base` is proved by a compiling reduction. Sorries remain in `exists_affine_sections_for_chosen_derivation` and `diagonalConormalDerivation_ext`, each with a corresponding node.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The DAG plan omits an explicit uniqueness step needed to pass from the canonical normalized derivation to a supplied normalized derivation; this delivery records that step as a separate intermediate node.

## New nodes
`stage3-diagonal-conormal-chosen` and `stage3-diagonal-conormal-uniqueness` are stated in `DiagonalConormalAffineSectionsChosen`.

## Second reading by W2

1. I compared the delivered base module with the repository version. The target theorem signature is byte-for-byte unchanged; the only interface addition is the proof-only import of the new decomposition module. Verdict: pass.
2. Both delivered files compile with `lcompile.py --all`. The base target has no `sorry`, and the only remaining sorries are the two explicitly named split theorems in `DiagonalConormalAffineSectionsChosen`; no forbidden declarations or hollow definitions occur. Verdict: pass.
3. The two split statements are strictly smaller than the target: one isolates the affine calculation for the canonical chosen derivation and the other isolates uniqueness. Their source, proof descriptions, and DAG nodes are present, and searches found no existing declaration matching them. Verdict: pass.
4. The proof follows the shortest available reduction through the canonical derivation and uniqueness, while retaining the unit's affine-coordinate route in the chosen-derivation node. No imports were removable: the base-change and conormal modules support the public target context, and the chosen module is proof-only. Verdict: pass.
5. The DAG proof and dependencies match the Lean proof: the target uses `stage3-diagonal-conormal-chosen` and `stage3-diagonal-conormal-uniqueness`, and both nodes point to the declarations in `DiagonalConormalAffineSectionsChosen`. Verdict: pass.

I changed only the target proof, added the proof-only decomposition module and its two nodes, and recorded this second reading. No existing statements or definitions were changed.
