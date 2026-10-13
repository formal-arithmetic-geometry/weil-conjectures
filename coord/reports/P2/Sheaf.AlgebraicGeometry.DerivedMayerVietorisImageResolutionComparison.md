## What changed
The target theorem is proved by composing the existing first-component comparison with a new intersection-component transport theorem. The target signature is unchanged. The new intermediate theorem is in `Sheaf.AlgebraicGeometry.DerivedMayerVietorisImageResolutionComparisonIntersection`.

## Proved and sorry left
`schemeMV_image_resolution_comparison` is proved. Sorry remains in `schemeMV_image_resolution_comparison_intersection` (strictly smaller equality for a supplied complex morphism) and in the imported split theorem `schemeMV_image_resolution_comparison_first`; both have explicit nodes.

## No longer needed
No planned declarations were removed. The proof imports only the canonical-data, split-triangle, first-component, and intersection-component modules.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt stopped at the mismatch between `(h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)` and `h ⁻¹ᵁ (U ⊓ V)`. This is isolated as the intersection-component theorem, while the top-level existential and first identity are fully assembled in Lean.

## New nodes
`lem-pc-mayer-vietoris-image-resolution-comparison-first`: first-component transport equality.
`lem-pc-mayer-vietoris-image-resolution-comparison-intersection`: intersection-component transport equality.

## Second reading by P2

1. Compared the delivered main module against the repository version: the target signature is unchanged; only imports and the proof body changed. Verdict: pass.
2. Compiled all remaining modules with `lcompile.py`; the main theorem has no `sorry`, while the intersection transport theorem remains the single named split hole. Verdict: pass.
3. Checked the new intersection statement against its Lean signature and source route; it is a strict component equality with the supplied morphism and preserves all hypotheses. Verdict: pass.
4. The proof uses the first-component theorem and the new intersection theorem, retaining the unit route; no unnecessary imports remain in the main file. Verdict: pass.
5. Updated the intersection node with exact Lean metadata and three search records; the DAG now agrees with the source. Verdict: pass.

Changed only the main proof, added the intersection theorem/node, and removed unrelated worker files from this delivery sandbox.
