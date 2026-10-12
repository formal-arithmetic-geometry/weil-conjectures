## What changed

Proved `AlgebraicGeometry.exists_isRegular_smooth_diagonal_generators` with its signature unchanged. The positive-dimensional case uses the existing proved source-library instance `isRegularImmersion_diagonal`, then upgrades weak regularity by proving the kernel proper at an image point. The dimension-zero case uses the etale diagonal's open image and an isomorphism on sections. Outside the image, an affine open in the complement gives the unit kernel. Updated the parent node's proof and dependencies accordingly.

Replaced the proof-only import of `Sheaf.AlgebraicGeometry.StandardSmoothAffineDiagonalGenerators` with proof-only imports of `WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion` and `Mathlib.AlgebraicGeometry.Morphisms.Etale`. All public imports and existing declaration signatures remain unchanged.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.exists_isRegular_smooth_diagonal_generators` (node `lem-sc-smooth-diagonal-regular-immersion`). Zero sorries remain in the delivered module; zero holes were added. Local compilation passes without warnings. The delivery tool also checks declaration axioms.

## No longer needed

Removed import and direct dependency: `Sheaf.AlgebraicGeometry.StandardSmoothAffineDiagonalGenerators`, node `lem-sc-standard-smooth-affine-diagonal-generators`. The separate Sheaf affine-generator proof branch is no longer needed by this theorem.

Removed direct planned dependency `lem-sc-standard-smooth-local-relative-dimension`; the existing source-library theorem already implements the standard-smooth chart argument. Its Mathlib module stays publicly imported for the statement's `SmoothOfRelativeDimension`.

The positive-dimensional proof uses the already proved blueprint node `lem-pur-diagonal-regular-immersion` as a tool; its standard-smooth chart proof follows the same geometric argument. The unit `sk-thm-picard-duality` has no realized statement or proof-step node requiring retention of the removed affine-generator dependency. No claim is made that removed branches are unreachable from every other target.

## Where the brief, the DAG or earlier work was wrong

The DAG planned a new Sheaf affine-diagonal calculation even though `WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion.isRegularImmersion_diagonal` already provides the needed weakly regular generators. Its notion is weak regularity at every ambient point, whereas the requested statement needs regularity only on the non-unit branch; the proof bridges this difference by a nontrivial inverse-image section ring.

No statement changes or new nodes. The second reading remains for the assigned independent reader.

## Second reading by F1

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only proof-only imports and the target proof changed. Verdict: pass.
2. Compiled `Sheaf.AlgebraicGeometry.SmoothDiagonalRegularGenerators` with `lcompile.py`; it succeeds with no warnings or sorries. The proof uses no forbidden declarations. Verdict: pass.
3. No statements were split off or added. The target's four cases (outside the image, dimension zero, positive dimension, and properness of the kernel) are mathematically valid and preserve the exact target strength. Verdict: pass.
4. The proof takes the existing regular-immersion diagonal result and Mathlib's etale diagonal route; the removed standard affine generator import is unnecessary. The unit route remains represented by the existing `lem-pur-diagonal-regular-immersion` dependency. Verdict: pass.
5. The node's proof, proof dependencies, and proof origin agree with the Lean proof; no new nodes are required. Verdict: pass.

I changed no Lean declarations or statements. I verified the proof by compilation and retained the pruned proof-only imports and DAG dependency updates recorded above.
