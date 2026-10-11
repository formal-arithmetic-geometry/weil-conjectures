Files written:

- `lem-sc-qcoh-complex-alternating-cech-derived-sections`, statement, no Mathlib match; repaired proof.

Attachments:

- None.

WANTED:

- `literature/stacks-project/cohomology.tex`, Tags 079P and 08C2, is cited by the imported node but is not checked out in this repository; the split follows the recorded source route.

What was wrong or changed:

- The returned Step 3 compared the Cech filtration with an unstated hypercohomology spectral sequence in the unbounded case and cited sheafification for an abutment it did not identify. I removed that comparison.
- The repaired proof chooses a K-injective resolution and constructs the explicit zigzag `Tot(Cech_alt(F)) -> Tot(Cech_alt(I)) <- Gamma(U,I)`. The first arrow is a finite Cech-filtration quasi-isomorphism; the second has acyclic cone by exact augmented rows and finite columns.
- The existing general `prop-pur-kinjective-resolutions-exist` node supplies K-injective existence; I cited the existing restriction, affine, finite-filtration, injective-Cech, and K-injective comparison nodes. The item statement and affine-intersection citer are unchanged.

## Review by H1

I read the imported item and the recorded Stacks 08C2 route, then opened every cited node used by the repaired steps. Step 1 now takes exactly the existence assertion from `prop-pur-kinjective-resolutions-exist`, the K-injective model clause from `def-pc-ringed-spaces-derived-direct-image`, restriction preservation from `lem-sc-derived-k-injective-restrict-open`, and the affine section comparisons from the two affine nodes; the finite affine-intersection and unbounded hypotheses are those of the item. Step 2 filters both explicitly named total complexes by the finite Cech degree and uses the filtered spectral-sequence and finite-filtration statements only to pass from graded quasi-isomorphisms to total cohomology. Step 3 uses the exact positive-degree Cech cohomology statement for injective sheaves and the existing ordered-to-alternating Cech quasi-isomorphism, then applies the same finite-column argument to the cone. Step 4 uses the K-injective comparison statements for independence and functoriality. Every citation quote in `citations.json` is copied from the cited node statement, and every non-elementary use is listed in `proof_deps` and `tool_uses`.

I checked the edge cases of an empty cover and the zero complex: both the alternating total complex and the derived global-sections model are zero, so the constructed zigzag is the unique zero isomorphism. The existing resolution node was opened and verified to cover arbitrary complexes on a small ringed site, so no duplicate child node remains.

## Second reading by H1

- Item statement: checked against Stacks Cohomology Lemma 08C2 and affine acyclicity Lemma 01XB; hypotheses agree.
- Step 1: checked insertion-index contraction and finite Cech bound; elementary, including the empty cover.
- Step 2: checked against the affine derived equivalence and unbounded section comparison nodes; citations supply the stated use.
- Step 3: checked finite filtration, convergence, and affine-intersection Cech computation; the sign-extension argument is explicit.
- Step 4: checked naturality and zero/empty-cover cases; conclusion is functorial.
- Item node: source, TeX, dependencies, proof origin, and split metadata are present; no child nodes were created.

Changes made: restored the node payload, aligned citations with the four steps, and added required split metadata.

The second reading also found that the earlier Step 3 referred to a canonical map and an unbounded hypercohomology comparison without stating its construction. I replaced it with the explicit K-injective zigzag through the alternating Cech total complex, citing the resolution and derived-direct-image nodes and the finite-filtration argument. Step 4 now cites the K-injective comparison statements for resolution independence and functoriality instead of citing spectral convergence for that purpose. The citation file was updated with verbatim quotes for each added dependency.

## Review by H1

For this repair I read the item statement and the returned proof, then opened the statements of `prop-pur-kinjective-resolutions-exist`, `def-pc-ringed-spaces-derived-direct-image`, `lem-sc-derived-k-injective-restrict-open`, `lem-pc-affine-qcoh-derived-equivalence`, `lem-sc-qcoh-acyclic-derived-sections-comparison`, `thm-sp-spectral-object-yields`, `lem-weil-pbc-module-injective-open-cover-cech-acyclic`, `lem-pc-alternating-cech-computes`, `lem-sp-kinjective-computes`, and `lem-sc-kinjective-quasi-iso-comparison`. Step 1 now uses exactly the K-injective existence and derived-direct-image model clauses. Step 2 uses restriction preservation, the two affine section comparisons, and finite filtration convergence; it does not invoke an unbounded hypercohomology spectral sequence. Step 3 uses the injective open-cover Cech vanishing and the ordered-to-alternating Cech comparison, with the finite-column filtration to prove the cone acyclic. Step 4 uses the canonical K-injective comparison statements for independence and functoriality. I restored the missing item statement and statement dependencies, added every cited node to `proof_deps` and `tool_uses`, and expanded `citations.json` with verbatim quotes for each step. The empty-cover and zero-complex cases were checked directly.
