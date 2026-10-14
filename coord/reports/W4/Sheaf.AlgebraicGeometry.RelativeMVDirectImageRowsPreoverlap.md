## What changed

The target is proved by applying a resolved-row core theorem and then an elementary
mate-cancellation theorem. The core supplies the two short exact rows, the strict
row map, six vertex isomorphisms, and three normalized equations under the
adjunction equivalence. The mate theorem applies the inverse equivalence and
cancels the chosen vertex isomorphisms. A generic homotopy-pullback row
strictification theorem is proved in
`RelativeMVHomotopyPullback.lean` and is recorded as a supporting DAG node.

## Proved and sorry left

The target declaration
`AlgebraicGeometry.relativeMV_direct_image_rows_preoverlap` is proved. The
mate-cancellation declaration
`AlgebraicGeometry.relativeMV_direct_image_rows_mates` and the generic
declaration
`AlgebraicGeometry.relativeMV_homotopyPullback_row_strictify` are proved.
The only sorry left is
`AlgebraicGeometry.relativeMV_direct_image_rows_core`, whose proof must
construct the geometric resolved rows and normalized equations from the stated
K-injective and Mayer--Vietoris ingredients.

## No longer needed

No imported statement or planned dependency was removed. The temporary
homotopy-pullback projection split was replaced by the proved
row-strictification construction, and no separate overlap-mate cancellation
node is needed.

## Where the brief, the DAG or earlier work was wrong

The target has no affine, quasi-compact, or quasi-separated hypotheses, so the
existing affine/qcqs SES presentation cannot be applied directly. The geometric
row construction is therefore isolated in the core theorem. Once its normalized
equations are available, the displayed target equations follow by the ordinary
inverse and cancellation laws for an adjunction equivalence; this algebraic step
does not require a second geometric theorem.

## New nodes

`lem-pc-relative-mv-direct-image-rows-core` is the one remaining split
obligation. `lem-pc-relative-mv-direct-image-rows-mates` records the proved
algebraic cancellation, and
`lem-pc-relative-mv-direct-image-rows-strictification` records the proved
generic mapping-cocone row construction.

## Second reading by W4

1. I compared the delivered preoverlap module with the repository version.
   The target theorem signature is unchanged byte for byte; only its proof,
   proof-only imports, and explanatory docstring changed. The new modules and
   declarations are recorded by fresh DAG nodes, and the target node changes
   only in its proof route and proof dependencies.

2. I compiled all four sandbox modules with `lcompile.py --all`. They compile
   without errors or warnings. There is no axiom, unsafe declaration, opaque
   declaration, extern, implemented-by declaration, or sorry in a definition.
   The sole remaining sorry is the named public theorem
   `relativeMV_direct_image_rows_core`, whose split node and source proof
   obligation are documented above. The mate and strictification theorems are
   proved by ordinary categorical cancellation and the mapping-cocone
   construction.

3. I checked the split statements against the existing library and Mathlib
   search records. The core theorem is strictly the geometric construction
   needed by the target; the mate theorem is a strictly smaller algebraic
   consequence; and the strictification theorem is a generic row construction.
   Their docstrings cite the Stacks tags and give complete proof plans. No
   split theorem merely restates the target.

4. The proof follows the shortest available route after the geometric core:
   the core supplies normalized equations, and the mate theorem applies the
   inverse adjunction equivalence and isomorphism cancellation. The target's
   old geometric imports are replaced by the core and mate modules; no planned
   dependency is discarded from the core's stated route. The unit remains
   `sk-thm-picard-coherence` and the resolved-row route is preserved.

5. The DAG records agree with the Lean declarations: the target depends on
   the core and mate nodes, the core depends on the strictification node and
   the stated geometric ingredients, and the new modules' declarations and
   statements match their node records. The remaining core hole is reported
   as a decomposition rather than as a completed proof.

I changed only the proof-only imports and proof of the target, added the
three supporting modules and their DAG nodes, and added this second-reading
record. No existing declaration signature or definition was changed.
