1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-flat-module-descent.json`: statement split, one affine reduction and common-stage proof.
- `dag/nodes/sec-picard-framework/lem-pc-affine-flat-module-descent.json`: new statement-only node; Mathlib searches found no match.

2. Attachments: none.

3. WANTED: none.

4. The returned affine statement was false: compatible transition maps and a colimit do not imply the tensor base-change isomorphisms required by Tag 02JO(3). I replaced it with the fixed-stage tensor formulation B_j = B_i tensor_{R_i} R_j, B = B_i tensor_{R_i} R and M_j, M obtained by tensoring M_i; the Noetherian hypothesis on R_i is explicitly removed. Its source is Algebra Lemma 10.168.1, Tag 02JO(3), rather than the limits lemma's quotation. The item statement was restored to the repository's merged TeX wording. Step 1 now cites the affine-local finite-presentation node and the module finite-presentation definition.

5. I checked the item and new node against the source, searched the whole DAG and blueprint for duplicates, ran LeanFinder, Loogle, and Mathlib grep searches, and verified the citation quotes are verbatim from each cited node statement; repaired the formerly empty uses list on step 1 by citing the scheme, morphism-convention, and base-change nodes. Small cases (identity system and zero module) satisfy the statement.

## Review by C1

I read `limits.tex`, Lemma 32.10.4 (Tag 05LY), and `algebra.tex`, Lemma 10.168.1 (Tag 02JO), including its exact part (3) hypotheses (a)--(c). The new affine node now states those tensor identifications and finite-presentation hypotheses, with no unnecessary Noetherian assumption. For item Step 1 I checked the finite affine cover node, the affine-local finite-presentation node, and `def-sc-finitely-presented-module`; each says the fact quoted in the step. Step 2 uses the new affine node's conclusion verbatim, and Step 3 is the elementary affine/stalk flatness criterion. I corrected the prior weak counterexample-prone statement, changed its source to 02JO(3), removed the meaningless directed-set convention citations from that node, restored the item's TeX statement, and added the missing finite-presentation citation and citation quotes.

## Not duplicates

lem-pc-affine-flat-module-descent vs lem-pc-flat-module-descent: the new node is the affine coordinate-module specialization used as a proof lemma; the existing item is the scheme-level assertion for quasi-coherent sheaves.
lem-pc-affine-flat-module-descent vs lem-pc-fp-complex-descent: the existing node descends finite-presentation complex data and does not assert flatness at any stage.
lem-pc-affine-flat-module-descent vs lem-pc-finite-flat-proper-support-descent: the existing node descends a bounded complex with proper supports, while the new node is the eventual flatness lemma for one module.
lem-pc-affine-flat-module-descent vs lem-pc-flat-bounded-complex-descent: the existing node constructs a descended complex and invokes eventual flatness; it does not state the affine module theorem.
lem-pc-affine-flat-module-descent vs lem-pc-noetherian-approximation-data: the existing node packages several Noetherian approximation properties, while the new node isolates module flatness.
lem-pc-affine-flat-module-descent vs lem-pc-recd-locally-principal: the existing node is the geometric relative effective Cartier divisor criterion (Tag 062Y), whereas the new node is the affine module flatness conclusion of Tag 02JO(3).
lem-pc-affine-flat-module-descent vs lem-weil-pbc-colimit-flat-ring-map: the existing node applies 02JO(3) only to the special module equal to the algebra C_i and concludes eventual flatness of ring maps; the new node handles an arbitrary finitely presented B_i-module M_i and its tensor base changes.

## Second reading by C1

- Item statement: checked directly against Stacks Limits Lemma 32.10.4 (Tag 05LY); repaired to include its morphism $X_i\\to Y_i$, quasi-coherent finite-presentation module, and flatness over the base-changed $Y_i$.
- Step 1: checked the finite affine-cover claim against `lem-weil-pbc-qcqs-finite-affine-open-cover` and the module/base-change notions against the cited definition nodes; added the finite-cover and quasi-coherence citations and repaired the cover to be on $Y_i$ and inverse images in $X_i$.
- Step 2: checked that `lem-pc-affine-flat-module-descent` now states the exact Tag 02JO(3) relative chart conclusion, and that directedness only supplies a common stage.
- Step 3: checked the affine-local flatness reduction on coordinate modules and stalks; expanded the previously compressed argument and confirmed it is elementary from the flatness definition and localization stability.
- New node `lem-pc-affine-flat-module-descent`: statement-only and self-contained with its definition dependencies; Tag 05LY affine form and all three recorded Mathlib searches were checked, with no exact Mathlib theorem found. Zero module, field base, and identity system cases are valid.

Changes made: added the existing finite-affine-cover and quasi-coherence citations to Step 1; expanded the affine cover and relative flatness argument; corrected both item and auxiliary statements to match Tags 05LY and 02JO(3); refreshed the auxiliary citation quote.

Second-reading correction: the source page for Tag 05LY was reread directly. Its statement includes a finite-presentation morphism $\\varphi_i:X_i\\to Y_i$ and flatness over the base-changed $Y_i$, so the item statement was corrected to include $Y_i$ and this relative flatness conclusion. The affine auxiliary node was corrected to the exact Tag 02JO(3) data $A_i\\to B_i$, $N_i$, with tensor base changes and flatness of $N_j$ over $A_j$; the former special case over $R_j$ was too weak for the source. Step 1 now covers affine opens of $Y_i$ and their inverse images in $X_i$, and Step 2 names the corresponding relative chart modules. The new statement dependency `pqf-def-coherent` and its verbatim citation were added. The identity system and zero module remain valid edge cases, and the field-base case reduces to ordinary base change.
