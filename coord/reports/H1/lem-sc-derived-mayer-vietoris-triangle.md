1. Files written: `dag/nodes/sec-picard-framework/lem-sc-derived-mayer-vietoris-triangle.json` (item, split); `dag/nodes/sec-picard-framework/lem-sc-derived-open-mayer-vietoris-ses.json` (statement node, unsplit, Mathlib generalization only); `citations.json` and this report.

2. Attachments: none.

3. WANTED: none; the cited Stacks source is identified as `literature/stacks-project/cohomology.tex`, Tag 08BU.

4. The source checkout contains no declaration tagged `lem-sc-derived-mayer-vietoris-triangle`; the nearby source Mayer–Vietoris declarations concern different `j_*` or pro-etale constructions. The existing QCoh node `lem-pc-derived-mayer-vietoris-triangle` is not a duplicate: it uses derived direct images `Rj_*` on qcqs schemes, whereas this item uses exact extension by zero `j_!` on arbitrary ringed spaces. The new node is the strictly weaker sheaf-level short exact sequence needed before forming the derived triangle.

## Review by H1

I read the item, its ancestor `lem-sc-finite-duality`, and the existing generic node `lem-weil-pbc-complex-ses-triangle`. I checked the new short exact sequence against Stacks Tag 08BU and verified that its hypotheses match the item: one ringed space, two opens covering it, and a sheaf of modules. Step 1 cites the new node for the degreewise lower-shriek sequence and the existing open-restriction node for exactness of both restriction and extension by zero; these statements provide exactly the two inputs used. Step 2 cites the existing generic theorem whose statement explicitly turns a degreewise short exact sequence of complexes into a distinguished triangle in the derived category. Step 3 cites the new node for the difference and counit maps and the exactness node for identifying termwise functors with their derived functors. I ran the required LeanFinder, Loogle, grep, and LeanSearch Mathlib searches for the new node; only generic Mayer–Vietoris sheaf primitives appeared, so it is not a Mathlib leaf. I also searched the DAG and blueprint for duplicate short exact extension-by-zero statements and found none. Small edge cases (U or V empty, and U intersection V empty) reduce to the zero extension sequence and remain covered by the same exactness statement.

## Second reading by H1

- Item statement: checked against Stacks `cohomology.tex`, Tag 08BU (`lemma-exact-sequence-lower-shriek`), hypothesis by hypothesis; verdict: correct after rendering all unions, restrictions, direct sums, and arrows in TeX.
- New node `lem-sc-derived-open-mayer-vietoris-ses`: checked against the short exact sequence in the Tag 08BU proof and the exact extension-by-zero node; verdict: correct, self-contained, and tested on empty opens and empty intersection.
- Step 1: checked that the short exact sheaf sequence applies termwise to a representative complex and that exactness is supplied by the cited node; verdict: supported.
- Step 2: checked that the cited short-exact-complex theorem gives exactly the displayed distinguished triangle in the derived category; verdict: supported.
- Step 3: checked the difference and counit maps against the Tag 08BU proof and the derived extension-by-zero adjunction node; verdict: supported and no longer marked elementary.
- New node form: both statements cite definitions for every introduced notion, use TeX once, name the Stacks tag and label, and contain no proof steps; Mathlib searches were rerun and found no exact declaration.

Changes made: corrected the item's `created.item` to this item, converted prose math to TeX, and added the existing derived adjunction dependency and citation so the derived-term identification is explicit.
