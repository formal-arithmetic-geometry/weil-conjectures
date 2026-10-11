Files written:
- `dag/nodes/sec-picard-framework/lem-pc-derived-tensor-second-factor-functor.json` (item, split; no Mathlib match)
- `dag/nodes/sec-picard-framework/lem-pc-kflat-tensor-quasi-iso.json` (statement-only child; no Mathlib match)
- `citations.json` (verbatim citations for every cited step dependency)

Attachments: none.

WANTED: none.

The source contains no exact sorry-free declaration for the item. The imported item had an empty proof. I added only the genuinely missing 064L tensor-invariance lemma; the remaining construction uses the existing K-flat resolution, tensor-complex, and derived-category definitions. No duplicate node was found.

## Review by C1
I checked the item against More on Algebra Tags 064L and 06Y6 and read every cited node before writing the proof. Step 1 uses exactly the new child statement. Step 2 uses the existing resolution existence and the definitions of K-flat complexes, total tensor complexes, and localization at quasi-isomorphisms to justify the derived functor and canonical comparisons. Step 3 uses the explicit cone and total-complex definitions; this is the elementary sign and cone calculation. Step 4 uses tensor functoriality, K-flat resolution choices, and the child quasi-isomorphism lemma for quasi-isomorphic second factors. I verified the one-point-site specialization and the A-action through N, and checked zero and degree-zero complexes as edge cases. Mathlib searches for the item and child used LeanFinder, Loogle, and source grep; only generic Tor/quasi-isomorphism results appeared.

## Not duplicates
lem-pc-kflat-tensor-quasi-iso vs lem-weil-derived-tensor-resolution-independent: the existing node is restricted to pro-etale sheaves, while the new node is the arbitrary one-point ring statement needed here.

## Second reading by C1
Step 1 checked against More on Algebra Tag 064L: the K-flat hypotheses, arbitrary second complex, one-point-site specialization, and induced total-tensor map agree; verdict pass.
Step 2 checked against Tag 06Y6: K-flat resolutions supply existence and Step 1 supplies invariance on comparison roofs, so localization gives the derived functor and canonical comparisons; verdict pass after making the roof argument explicit.
Step 3 checked against the total-complex and abstract-derived-category definitions: the cone summands, block differential signs, and shift reindexing are explicitly identified; verdict pass after expanding the former handwave.
Step 4 checked against Tag 06Y6 and the K-flat definition: functoriality is chain-level, and for a quasi-isomorphism of fixed factors the cone is acyclic and remains acyclic after tensoring with K-flat F; verdict pass after correcting the invalid application of the child lemma.
New node `lem-pc-kflat-tensor-quasi-iso` checked against Tag 064L hypothesis by hypothesis, including arbitrary complex N and K-flat source and target; verdict pass. Its statement is self-contained with definition dependencies, TeX, source tag, and recorded Mathlib searches.
Small cases checked: zero complexes give zero total complexes; a field makes every complex K-flat; the empty/one-point site specialization is exactly the ring-complex statement; degree-zero and n=0/1 shifts reduce to ordinary tensor and its cone.
Changes: expanded Step 2's localization argument over comparison roofs; expanded exactness in Step 3 to an explicit cone and shift calculation; replaced Step 4's incorrect child-lemma use by the K-flat cone argument; added verbatim citations and corrected the item's created-item metadata.
