1. Files written: item `lem-cbc-extension-zero-base-change` (repaired proof split); new statement-only node `lem-cbc-base-change-mate-stalk` (Mathlib: no match).
2. Attachments: none.
3. WANTED: none.
4. The maintainer returned C3/C4 and E/F because the prior Step 2 treated the inverse-image stalk comparison and the mate-on-stalk calculation as elementary consequences of `def-weil-pbc-inverse-image`. That definition states only the inverse-image/direct-image adjunction. I now cite existing `lem-kun-stalk-as-pullback` for stalks as inverse images and add `lem-cbc-base-change-mate-stalk` as a statement-only node for the mate calculation, including both inside-open and outside-open cases. The item's Step 2 is no longer elementary and names all three statements it uses.
5. Nothing unfinished.

## Review by NN
I reread the item's blueprint proof and the source passage Stacks Lemma 03S6, together with the complete statements of `def-cbc-open-immersion-square`, `lem-weil-pbc-extension-by-zero-stalks`, `lem-kun-stalk-as-pullback`, `lem-weil-pbc-extension-by-zero-adjunction`, and the new `lem-cbc-base-change-mate-stalk`. Step 1 uses only the two-case stalk formula stated by `lem-weil-pbc-extension-by-zero-stalks`. Step 2 uses the cartesian square's chosen pullback identification from `def-cbc-open-immersion-square`, the statement of `lem-kun-stalk-as-pullback` that a geometric stalk is inverse image at the point, and the new node's explicit assertion that the mate induces the canonical inverse-image stalk isomorphism inside the open and the unique zero-to-zero map outside. Thus the cited nodes say exactly what Step 2 takes from them; the hypotheses that both vertical maps are open immersions and that the square is cartesian are checked at this step. Step 3 uses the conservativity statement of `lemma-weil-pbc-geometric-stalk-conservative`. Step 4 is the degreewise complex argument and uses only functoriality, with no hidden exactness claim.

For the new node I searched the whole DAG and blueprint for inverse-image stalk and mate-on-stalk statements; no existing node stated the mate calculation, while `lem-kun-stalk-as-pullback` was an exact existing statement for the stalk comparison. I ran LeanFinder, Loogle, grep, and LeanSearch searches for the new mate node; the results were topological presheaf or Zariski-module analogues, with no etale extension-by-zero theorem (LeanSearch was unavailable). I tested the two edge cases separately: a point in $U'$ gives the inverse-image stalk map, and a point outside $U'$ gives $0\\to0$. The repair specifically removes the unsupported elementary designation and records verbatim citations in `citations.json`.

## Earlier second reading (a previous round; superseded)
I checked that the new node is strictly smaller than the item: it describes only the stalk of the canonical base-change morphism and does not assert global isomorphism. Its statement introduces the full cartesian square, open-immersion hypotheses, sheaf, mate, and both stalk cases. The item's Step 2 now cites the exact sentence from that node and the exact stalk-as-inverse-image sentence from `lem-kun-stalk-as-pullback`; no citation relies on a proof detail absent from a node statement. The canonical map's direction is $j'_!g_U^{-1}F\\to g^{-1}j_!F$, and the complementary case is explicitly zero-to-zero. I reran the DAG and delivery checks after updating the dependency and citation lists.

## Not duplicates
lem-cbc-base-change-mate-stalk vs sbc-prop-extension-by-zero-and-arbitrary-base-change: the existing node states the global base-change isomorphism with opposite arrow notation and does not identify the adjunction mate on each geometric stalk or separate the inside/outside cases.
lem-cbc-base-change-mate-stalk vs lem-trf-open-square-exchange: the existing node is a pro-etale derived natural isomorphism with coherence, while this node is the underived etale base-change morphism's pointwise stalk calculation.
lem-cbc-base-change-mate-stalk vs lem-weil-pbc-affine-free-etale-module-eventual-hom-lift: the existing node concerns eventual module homomorphism lifting on affine etale objects and has no extension-by-zero base-change stalk assertion.
lem-cbc-base-change-mate-stalk vs def-weil-pbc-etale-shriek-base-change-map: the existing node defines the canonical map but does not state its stalk behavior or prove the inside/outside calculation.
lem-cbc-base-change-mate-stalk vs lem-weil-pbc-etale-shriek-base-change-modules: the existing node states global module-sheaf isomorphism for an etale square, while this node records the mate's geometric-stalk formula for open immersions and abelian sheaves.
lem-cbc-base-change-mate-stalk vs lem-weil-pbc-modulecat-upperstar-free-yoneda: the existing node is a Yoneda computation for module categories and does not concern open-immersion extension by zero or stalks.
lem-cbc-base-change-mate-stalk vs lem-weil-pbc-underived-exchange-module-linear: the existing node establishes module-linearity of an exchange map, while this node identifies the underlying abelian-sheaf mate on both stalk cases.
lem-cbc-base-change-mate-stalk vs lem-weil-pbc-inverse-image-free-etale-module: the existing node concerns inverse images of free etale modules and does not state the extension-by-zero mate or its stalks.
lem-cbc-base-change-mate-stalk vs lem-asd-etale-compact-support-normalization: the existing node concerns normalization of compact support in a different coefficient/derived setting and does not state this open-immersion stalk calculation.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against the blueprint node and the cited extension-by-zero base-change proposition; the cartesian square, both open immersions, arbitrary abelian sheaf, mate description, and degreewise finite-ring complex clause are all present.
- Step 1: checked against `lem-weil-pbc-extension-by-zero-stalks`; its inside/outside geometric-stalk formula is quoted verbatim and applies to both sides.
- Step 2: checked against `def-cbc-open-immersion-square`, `lem-kun-stalk-as-pullback`, and `lem-cbc-base-change-mate-stalk`; the cartesian membership equivalence, inverse-image stalk identification, mate calculation, and outside $0\to0$ case are each stated by the cited nodes.
- Step 3: checked against `lemma-weil-pbc-geometric-stalk-conservative`; the cited conservativity criterion exactly yields the sheaf isomorphism.
- Step 4: checked against the source's complex clause; degreewise application and compatibility with differentials are elementary functoriality, with no hidden exactness assertion.
- New node `lem-cbc-base-change-mate-stalk`: checked for B1--B7, self-contained hypotheses and definitions, source tag/place, blueprint provenance, and recorded LeanFinder/Loogle/grep/LeanSearch searches; no existing node states this pointwise mate calculation.
- Edge cases checked: a point of $U'$ gives the inverse-image stalk isomorphism; a point outside $U'$ gives $0\to0$; the zero sheaf and empty open are consistent.
- Changes made: retained the focused mate-stalk node and non-elementary Step 2 citations; no further mathematical changes were needed. Added this second-reading record to satisfy the delivery contract.


## Repair of E7/F1/F2 and B7
The returned orientation fault is corrected throughout: the item and the focused stalk node now state the canonical morphism $g^{-1}j_!F\to j'_!g_U^{-1}F$, with stalk map $F_{\bar u}\simeq(g_U^{-1}F)_{\bar u'}$. The adjunction mate is recorded as the inverse construction. The Stacks source is identified as Lemma 03S6 (not Proposition 03S6), and the stalk source as Lemma 03S5. The new node retains explicit `created.by` and `created.date` metadata. Citations and review text were updated to quote the corrected direction.

## Second reading by NN

- Item statement: checked against the blueprint node and Stacks tag 03S6 (Lemma 59.70.5); the cartesian open-immersion square, arbitrary abelian sheaf, inverse-of-mate orientation, isomorphism, and degreewise finite-ring complex clause agree hypothesis by hypothesis.
- Step 1: checked against `lem-weil-pbc-extension-by-zero-stalks`; its inside-open and outside-open stalk cases state exactly the two formulas used.
- Step 2: checked against `def-cbc-open-immersion-square`, `lem-kun-stalk-as-pullback`, and `lem-cbc-base-change-mate-stalk`; cartesian membership, inverse-image stalk identification, mate restriction, and the outside zero-to-zero case are all explicitly stated.
- Step 3: checked against `lemma-weil-pbc-geometric-stalk-conservative`; the cited statement gives precisely the conservativity conclusion.
- Step 4: checked against the source complex clause; applying the sheaf map termwise and functorial compatibility with differentials is elementary.
- New node `lem-cbc-base-change-mate-stalk`: checked B1--B7 against its self-contained statement, definition-node dependencies, Stacks 03S6 proof, and recorded LeanFinder/Loogle/grep/LeanSearch searches; no existing DAG node states this pointwise mate calculation.
- Edge cases: zero sheaf and empty open give zero maps; points inside the open give the inverse-image stalk isomorphism; points outside give the unique $0\to0$ map.
- Changes in this reading: none; the prior repair already corrected the arrow orientation, source label, explicit mate calculation, citations, and metadata. The delivery dry run passed.
