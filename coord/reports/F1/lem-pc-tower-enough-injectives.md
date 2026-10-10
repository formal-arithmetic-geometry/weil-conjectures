Files written:

- `lem-pc-tower-enough-injectives.json`, statement node, split (no Mathlib leaf).
- `lem-pc-small-diagram-grothendieck-enough-injectives.json`, statement-only node, Mathlib search verdict: no match.
- `citations.json`.

Attachments: none.

WANTED: literature/stacks-project/more-algebra.tex, Tag 07KW, because the source checkout is not present on this machine; the repository citation index confirms the tag and label.

The item had no exact declaration tagged `lem-pc-tower-enough-injectives` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`. The imported statement is retained. I checked the whole DAG for `07KW`, tower/inverse-system, and diagram-category statements. The existing `lem-pc-tower-abelian` node supplies the abelian-category clause; it does not state the Grothendieck property or enough injectives. The new node is strictly structural: it asserts the Grothendieck property, not the item's enough-injectives conclusion, and carries only a statement as required for an unsplit child.

## Not duplicates

lem-pc-small-diagram-grothendieck-enough-injectives vs lem-pc-tower-enough-injectives: the new node states that the tower category is Grothendieck abelian, while the item states the consequence that it has enough injectives.
lem-pc-small-diagram-grothendieck-enough-injectives vs lem-pc-tower-abelian: the new node adds the Grothendieck property, while the existing node states only abelianness.
lem-pc-small-diagram-grothendieck-enough-injectives vs lem-pc-tower-limit-left-exact: the new node concerns the ambient category's Grothendieck axioms, while the existing node concerns the inverse-limit functor's exactness.
lem-pc-small-diagram-grothendieck-enough-injectives vs lem-pc-derived-limit-roos-abelian-groups: the new node concerns categorical existence of injectives, while the existing node computes derived inverse limits by the Roos complex.
lem-pc-small-diagram-grothendieck-enough-injectives vs lem-pc-tower-surjective-lim-acyclic: the new node concerns the whole tower category, while the existing node concerns acyclicity of surjective towers.
lem-pc-small-diagram-grothendieck-enough-injectives vs lem-pc-abelian-groups-exact-products: the new node asserts Grothendieck structure of towers, while the existing node asserts exactness of products in abelian groups.
lem-pc-small-diagram-grothendieck-enough-injectives vs lem-weil-pbc-mittag-leffler: the new node is about injectives in all towers, while the existing node is about Mittag--Leffler finite-group towers.
lem-pc-small-diagram-grothendieck-enough-injectives vs prop-weil-pbc-roos-triangle: the new node is about the abelian category structure, while the existing node constructs a Roos triangle in a different tower category.

## Review by F1

I read the target node, its unit and chapter records, the existing tower-abelian node, and the source citation recorded for Stacks Tag 07KW. Step 1 uses exactly the new node's conclusion, specialized to the small natural-number indexing category and the Grothendieck abelian category of abelian groups. Step 2 uses the existing tower-abelian statement only for the category identification and abelian structure; its quoted statement says precisely that inverse systems indexed by the natural numbers with levelwise maps form an abelian category. The remaining identification of inverse systems with functors and natural transformations is definitional and marked elementary. The hypotheses (small index category and Grothendieck abelian target) were checked before applying the new node. I tested the specialization on the zero tower and on a constant tower; both are ordinary functor-category objects and the conclusion has the expected meaning. Mathlib searches were run for the item and the new general node using LeanFinder, Loogle, grep, and LeanSearch; the unavailable LeanSearch service is recorded as unavailable rather than as a negative result.

## Second reading by F1

- Item statement: checked against More on Algebra Tag 07KW, Lemma 15.88.1 and its proof footnote; the tower category and enough-injectives conclusion agree hypothesis by hypothesis, including the natural-number indexing.
- Step 1: checked against the new embedding node and `lem-pc-tower-abelian`; the cited statements provide the levelwise injective split tower and the ambient abelian category. Replaced the unsupported Grothendieck-category route.
- Step 2: checked against the embedding node and the definitions of injective object and enough injectives; the recursive lift is written explicitly using a section of each split surjection and extension into its injective kernel.
- `lem-pc-tower-injective-embedding`: checked against Tag 07KW's proof footnote; statement is self-contained, defines all tower/group/injective notions by nodes, uses TeX once, and was tested on the zero and constant towers. LeanFinder, Loogle, grep, and LeanSearch searches were run and recorded; LeanSearch was unavailable.

Changes made: removed `lem-pc-small-diagram-grothendieck-enough-injectives` because Tag 07KW does not state that theorem; added `lem-pc-tower-injective-embedding` for the actual source construction; rewrote both proof steps and citations to remove the unsupported Grothendieck assertion and to spell out the compatible lifting argument.

## Not duplicates

`lem-pc-tower-injective-embedding` vs `lem-pc-tower-enough-injectives`: the new node supplies the levelwise-injective split tower embedding; the item concludes enough injectives using the lifting argument.
`lem-pc-tower-injective-embedding` vs `lem-pc-tower-limit-left-exact`: the new node constructs injective towers; the existing node concerns left exactness of inverse limit.
`lem-pc-tower-injective-embedding` vs `lem-pc-tower-abelian`: the new node gives an embedding construction; the existing node only states that the tower category is abelian.
`lem-pc-tower-injective-embedding` vs `lem-pc-derived-limit-roos-abelian-groups`: the new node constructs injective objects; the existing node computes derived limits.
`lem-pc-tower-injective-embedding` vs `lem-pc-tower-surjective-lim-acyclic`: the new node concerns embeddings into injective towers; the existing node proves acyclicity of surjective towers.
`lem-pc-tower-injective-embedding` vs `lem-pc-abelian-groups-exact-products`: the new node concerns tower transitions; the existing node concerns exact products in abelian groups.
`lem-pc-tower-injective-embedding` vs `lem-weil-pbc-mittag-leffler`: the new node constructs injective towers; the existing node proves Mittag--Leffler vanishing for finite towers.
`lem-pc-tower-injective-embedding` vs `prop-weil-pbc-roos-triangle`: the new node is about ordinary abelian-group towers; the existing proposition is a derived Roos triangle for pro-etale coefficient towers.
