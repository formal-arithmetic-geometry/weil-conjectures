# Delivery report

1. Files written:

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-site-restriction-injectives.json`: split item; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-site-restriction-adjunction.json`: statement-only child; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-site-extension-by-zero-exact.json`: statement-only child; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-site-restriction-exact.json`: statement-only child; no Mathlib match.

2. Attachments: none.

3. WANTED: none.

4. I found no sorry-free declaration tagged with the item id in `WeilConjectures` or `Comparator`. The existing DAG node `lem-weil-pbc-cohomology-over-object-localization` uses this item for the adjunction and exactness facts, so I kept the split strictly below that item and did not cite the parent from its own proof. Searches of the DAG and blueprint found no existing node stating any of the three child assertions. The parent statement remains unchanged; its statement dependencies now name the three child facts as well as the site and abelian-category definitions.

## Review by K1

I read the parent node and the ancestor blueprint clause in `lem-sc-artin-schreier-dimension`, and checked the source passage in `literature/stacks-project/sites-modules.tex`: Section 03DH supplies the extension-by-zero adjunction and Lemma 03DJ supplies exactness of extension by zero and restriction. The parent proof has four steps. Step 1 uses only the localized-site definition from `def-weil-pbc-sites-and-cohomology`; Steps 2, 3, and 4 cite respectively the adjunction, extension exactness, and restriction exactness child statements, and each quoted sentence is copied into `citations.json`. I read each child statement to verify that it introduces the same Grothendieck site, slice topology, abelian sheaf categories, functor, and exact sequence hypotheses used by its parent step. The children contain statements only, as required for unsplit nodes.

I tested the formulations on the identity object $W$ (where the slice is the original site and extension/restriction are identities), on the terminal object, and on the zero sheaf. I also ran LeanFinder, Loogle, and Mathlib-source grep through `msearch.py` for each child; results were generic sheaf adjunction or sheafification infrastructure and no exact arbitrary-site theorem, so no child is marked as a Mathlib leaf. The parent item searches already recorded the same negative result. The only correction made was to replace the empty parent proof with the four sourced steps and add the three strictly smaller statement dependencies.
