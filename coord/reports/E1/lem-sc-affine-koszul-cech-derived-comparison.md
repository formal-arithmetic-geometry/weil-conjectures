# Stage 1 report

1. Files written: item `lem-sc-affine-koszul-cech-derived-comparison` (split); new node `lem-sc-affine-koszul-hom-alternating-cech` (statement, unsplit, Mathlib no match); `citations.json`.
2. Attachments: none.
3. WANTED: `literature/stacks-project/perfect.tex`, Tags 08D1 and 08D2, for `lem-sc-affine-koszul-cech-derived-comparison` and `lem-sc-affine-koszul-hom-alternating-cech`. The packet is absent locally; the proof is an agent reconstruction of the cited comparison.
4. The item had no proof and no sorry-free Lean declaration. Existing DAG nodes already cover alternating Cech normalization (`lem-pc-alternating-cech-computes`) and the affine Cech resolution (`lem-pc-cech-resolution`), so I did not duplicate either. The missing real lemma is the module-level filtered Koszul Hom to alternating Cech quasi-isomorphism, recorded as `lem-sc-affine-koszul-hom-alternating-cech`.
## Not duplicates

lem-sc-affine-koszul-hom-alternating-cech vs lem-pc-qcoh-truncation-derived-limit: the existing node proves derived inverse-limit compatibility for truncation towers (Tag 08D1), whereas the new node proves the Koszul Hom filtered-colimit to alternating Cech localization quasi-isomorphism; neither statement specializes to the other.

## Review by E1

I checked the item's source tags and blueprint ancestor `lem-sc-finite-duality`, but the cited `perfect.tex` packet is absent locally, so this proof is my reconstruction rather than a source transcription. I read the existing statements of every cited node. Step 1 uses exactly the new node's assertion that the filtered Koszul Hom colimit maps quasi-isomorphically to the localized alternating Cech total complex. Step 2 uses the existing Cech resolution's statement that its non-augmented terms are acyclic and computes derived pushforward, the acyclic-resolution theorem's canonical identification with derived functors, and the K-injective existence statement. Step 3 uses affine derived equivalence to identify sections of associated quasi-coherent complexes with the module complex and its localizations. I verified that each quote in `citations.json` is verbatim from the cited node statement, that all proof dependencies are listed, and that the edge cases r=0 and the zero complex are explicitly covered. I ran the required LeanFinder, Loogle, grep, and LeanSearch searches for the item and new node; LeanSearch was unavailable, recorded as such, while the other searches returned no matching Mathlib declaration.

## Second reading by E1

- Item statement: checked against the available DAG parent `lem-sc-affine-perfect-open-represent-cohomology` and the stated Stacks Tags 08D1/08D2; hypotheses $A$, affine $X$, finite principal cover, quasi-coherent complex, and the derived-sections conclusion agree. The source TeX packet is absent locally, so the tag-level comparison is recorded as a reconstruction.
- New node `lem-sc-affine-koszul-hom-alternating-cech`: checked for B1--B7; it is statement-only, self-contained, uses TeX delimiters, cites the Koszul, Cech, cochain, and Hom-complex definitions, and records all required searches. Tested on a field, the zero complex, $r=1$, and the empty-cover convention $r=0$.
- Step 1: checked against the new node's filtered Hom-to-localized-Cech assertion; the transition maps, localization map, and differential compatibility are now written explicitly.
- Step 2: checked against `lem-pc-cech-resolution`, `lem-pc-derived-acyclic-resolution`, and `prop-pur-kinjective-resolutions-exist`; the affine principal intersections and K-injective totalization are exactly the cited inputs.
- Step 3: checked against `lem-pc-affine-qcoh-derived-equivalence`; the section/localization identity and compatibility with every Cech face map are stated explicitly and the zero/empty-cover cases are recorded.
- Citations: refreshed the step-1 quote so it is verbatim after the TeX repair; all other quotes remain verbatim.

Changes made: corrected the item `created.item` ownership, added the missing `def-pur-hom-complex` statement dependency, repaired the new node's TeX and localization notation, expanded the transition/differential argument in step 1, expanded the affine localization argument in step 3, and refreshed the citation quote.
