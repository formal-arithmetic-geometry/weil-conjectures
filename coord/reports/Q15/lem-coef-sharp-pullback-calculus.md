# Worker report: lem-coef-sharp-pullback-calculus

## Files written

- `dag/nodes/sec-six-functors/lem-coef-sharp-pullback-calculus.json`: existing item split into seven proof steps; no new nodes; Mathlib searches found no exact match.
- `citations.json`: verbatim statement excerpts for every cited dependency and step.

## Attachments

None. I searched the slopmaster2 source for the item id, sharp-map terminology, and the relevant declarations; no sorry-free project declaration states this item exactly.

## WANTED

WANTED: Rezk, “Fibrations and Homotopy Colimits of Simplicial Sheaves”, Section 2 and Proposition 2.7 (and its Section 2 base-change, pasting, and product consequences), https://rezk.web.illinois.edu/rezk-sharp-maps.pdf, for `lem-coef-sharp-pullback-calculus`; the PDF is not archived in `literature/`.

## What was wrong or incomplete in the imported node

The imported node had the correct statement and dependency on `lem-coef-kan-quillen-right-proper`, but it had no proof, no proof origin, and no split report. I supplied the source-based proof and added the existing Brown fibrant-localization pullback node where the coherent pullback comparison is used. I did not create a node for any clause of the item, since that would merely restate the item. The source document is online rather than archived, so the proof origin is recorded as agent reconstruction from the blueprint paragraph and the cited paper.

## Review by Q15

I read the item node, the fixed `sec-six-functors` chapter record, and unit `sk-prop-sf-biduality-general`. I read the full statements of `lem-coef-kan-quillen-right-proper` and `lem-coef-brown-fibrant-localization-pullbacks`, including their hypotheses and conclusions, and used only claims those statements supply: functorial fibrant replacement and homotopy-pullback independence, right properness, and natural limiting pullback cones. The imported item has no Lean declaration in `/home/ubuntu/weil-src-slopmaster2` or the archived upstream reference.

Step 1 checks the homotopy-pullback model against the Kan--Quillen statement. Step 2 proves both directions of Rezk’s sharpness criterion: forward comparison uses right properness and the weak-equivalence/fibration replacement; reverse comparison uses a replacement of an arbitrary map to the base and the same homotopy-pullback model. Step 3 derives arbitrary base change directly from the definition and then specializes to products; it uses no external node. Step 4 checks the canonical map to the strict pullback and uses the cited replacement-independence statement to identify homotopy-cartesianness. Step 5 checks both sharpness hypotheses before base-changing the square and uses right properness plus natural pullback comparisons to obtain the weak-equivalence comparison and its equivalent homotopy-cartesian formulation. Step 6 applies that comparison to two adjacent squares and then to their products, using the Brown node’s naturality clause for the coherent square comparison. Step 7 identifies the final displayed product square as a strict pullback of the sharp product map.

I checked edge cases explicitly: the empty simplicial set as a base-change object, identity and terminal maps, an identity weak equivalence in the criterion, and an arbitrary (possibly non-Kan) product factor handled through the functorial replacement model. The proof dependencies are exactly the union of the step uses, and no cycle or duplicate new node was introduced. Mathlib searches (LeanFinder, Loogle, grep, and LeanSearch) found only ordinary Kan-fibration, pullback-pasting, or universally stable morphism-property declarations, with no sharp-map or homotopy-cartesian theorem.

## Second reading by Q15

I read Rezk, *Fibrations and Homotopy Colimits of Simplicial Sheaves*, Section 2, especially the definition on printed p. 3 (PDF lines 118–136), Lemma 2.5 (lines 181–204), and Proposition 2.7 and its proof (lines 205–218). The item statement agrees hypothesis by hypothesis: simplicial sets are the stated Kan–Quillen model category, sharpness is universal strict-pullback homotopy-cartesianness, the weak-equivalence pullback criterion is the right-proper characterization, and the base-change, product, canonical-map, comparison, pasting, and final product-square clauses quantify over the same maps and objects. Identity maps, terminal maps, the empty simplicial set, and arbitrary (including non-Kan) product factors satisfy the statement.

Step 1: checked against Rezk’s homotopy-cartesian definition (2.3) and the Kan–Quillen replacement-independence statement; verdict correct. Step 2: checked against Proposition 2.7’s factorization diagram (2.6), including both directions and the right-proper pullback argument; verdict correct after making simultaneous replacements of both cospan legs and of (p) explicit. The Brown-localization citation was removed because its statement does not provide the simplicial-set comparison used here. Step 3: checked against the definition’s immediate base-change closure (p. 3, lines 134–136); verdict correct and elementary, including the product projection specialization. Step 4: checked against Proposition 2.7’s pullback comparison and the existing homotopy-pullback pasting node; verdict correct after explicitly identifying the identity-base square with the weak-equivalence test. Step 5: checked by forming the replacement cube, applying right properness to each replacement pullback, and using the sharpness hypotheses to identify strict and derived pullbacks; verdict correct after replacing the former Brown citation and spelling out the cube argument. Step 6: checked against the existing homotopy-pullback pasting node and the same replacement cube; verdict correct after replacing the former Brown citation and stating why products are degreewise pullbacks and preserve the replacement comparison. Step 7: checked directly from the strict pullback ((E\times L)\times_{B\times L}(B\times K)\cong E\times K) and Step 3; verdict correct and elementary.

There are no new nodes: the item’s seven steps use only the existing Kan–Quillen right-proper node and the existing homotopy-pullback pasting node. I removed all citations to `lem-coef-brown-fibrant-localization-pullbacks`, because its localization statement does not say the simplicial model-category facts claimed in the worker’s Steps 2, 5, or 6, and updated `citations.json` with verbatim excerpts from the two actual dependencies. The repaired proof dependency set is exactly the union of the step uses; no statement or blueprint field was changed, no SGA source is used, and no duplicate or Mathlib leaf was introduced.
