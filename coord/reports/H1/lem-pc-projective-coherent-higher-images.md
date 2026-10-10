1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-projective-coherent-higher-images.json`: split item, one new proof dependency, four recorded Mathlib searches.
- `dag/nodes/sec-picard-framework/lem-pc-cech-localization-higher-images.json`: statement-only child; Mathlib searches found no match.
- `citations.json`: verbatim quotes for every cited node in every item step.

2. Attachments: none. The source declaration `isFinitePresentation_higherDirectImage_of_isClosedImmersion` is sorry-free, but the item's required vanishing clause is `isZero_higherDirectImage_of_isClosedImmersion`, whose proof is `sorry`; therefore the combined item is not an attachment.

3. WANTED: none.

4. What I checked and corrected:

The project source `WeilConjectures/AlgebraicGeometry/Cohomology/Projective.lean`, lines 143--172, was read for both declarations and their docstrings. The coherence theorem matches the first clause, while the vanishing theorem remains sorried. I read the existing nodes `lem-pc-projective-coherent-finiteness`, `lem-pc-cech-computes`, and `pqf-lem-coherent-ft-locnoeth`; their statements support exactly the uses recorded in steps 1--3. The imported step 2 used the non-elementary assertion that the restricted Cech complex localizes term by term without citing a node, so I created `lem-pc-cech-localization-higher-images` as a smaller statement-only node and cited its exact statement. I added the missing scheme statement dependency and filled the blueprint references. The item was tested on the edge cases $a=1$ (unchanged complex) and $a=0$ (zero localization and empty principal-open fibre); the child statement has the expected zero-complex behavior. Mathlib searches were run for both the item and child; LeanSearch was unavailable and recorded as such.

5. What I could not finish:

The new localization child remains unsplit by design; its proof is a separate stage-1 queue item.

## Review by H1

I checked each cited statement directly in its node file. Step 1 takes finite $A$-modules and the vanishing bound from `lem-pc-projective-coherent-finiteness`. Step 2 takes the termwise localization and localized cohomology identity from the new child, then the Cech-to-cohomology equality from `lem-pc-cech-computes`; the hypotheses (finite affine cover, affine intersections, and quasi-coherence) are the hypotheses stated in those nodes and in the item setup. Step 3 takes the equivalence between coherence and quasi-coherent finite type from `pqf-lem-coherent-ft-locnoeth`, with $A$ Noetherian and $M^q$ finite as established in steps 1--2. I corrected the missing step-2 citation, added its dependency to `proof_deps`, filled `blueprint.from`/`same_as`, and recorded the exact citation quotes in `citations.json`.

## Not duplicates

lem-pc-cech-localization-higher-images vs lem-pc-cohomology-sections-affine-base: the new node identifies the localized finite Cech complex and its cohomology on each principal open; the existing 01XK node identifies global sections of higher direct images with cohomology over an affine base and does not state termwise Cech localization.
lem-pc-cech-localization-higher-images vs lem-pc-flat-base-change-cohom: the new node is a principal-open localization calculation for one affine-base cover; the existing 02KH node is a flat base-change isomorphism for higher direct images and does not state the Cech localization identity.

## Second reading by H1

- Step 1 checked against the projective finiteness node and its affine Noetherian hypotheses; finite-module and $q>n$ conclusions match.
- Step 2 checked term by term against `pqf-lem-associated-sections-localize` and `lem-pc-cech-computes`; affine intersections, principal localization, finite products, and exact localization are accounted for.
- Step 3 checked against `lem-weil-pbc-higher-direct-image-presheaf`, `pqf-lem-associated-sections-localize`, and `pqf-lem-coherent-ft-locnoeth`; the sheafification and coherence conclusion match the stated hypotheses.
- The child `lem-pc-cech-localization-higher-images` was retained, but narrowed and corrected to the exact principal-open Cech localization fact used by step 2, with Stacks Tag 01XK as its source.
- Updated step 2 and step 3 citations and proof dependencies; step 3 now uses the same-unit finite-support node for quasi-coherence, avoiding an undeclared cross-unit tool.
- Edge cases checked: $a=1$ leaves the Cech complex unchanged, $a=0$ gives the zero localization and empty principal-open restriction, and $X=\\operatorname{Spec}(A)$ has only degree-zero cohomology.
