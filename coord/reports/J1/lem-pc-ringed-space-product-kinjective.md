Files written:

- `dag/nodes/sec-picard-framework/lem-pc-ringed-space-product-kinjective.json`: statement split; no new nodes; Mathlib searches found no exact product-closure theorem.

Attachments:

- None.

WANTED:

- None; `literature/stacks-project/derived.tex` is available and Tag 0BK6 was read.

What I checked and corrected:

- The source item is the Stacks Project lemma `derived.tex`, Tag 0BK6 (`lemma-product-K-injective`). No declaration tagged with the item exists in either Lean checkout, and the nearby project Products file only provides the generic derived-category product instance, not this exact statement.
- I read the existing statements of `def-pur-kinjective-complex`, `lem-weil-pbc-kinjective-hom-derived`, and `def-weil-category-product`. Step 1 uses only the K-injective definition: componentwise null-homotopies assemble into a null-homotopy. Step 2 is the direct termwise chain-map and homotopy calculation. Step 3 uses exactly the cited K-injective Hom bijection and the product universal property to pass from the homotopy category to the derived category.
- I added `def-weil-category-product` to `stmt_deps`, since the conclusion explicitly invokes the categorical product notion. I kept the item hypotheses unchanged and did not create a duplicate node.
- I checked singleton and empty index families: the argument reduces respectively to the original K-injective complex and the zero/product terminal complex, with the same componentwise reasoning.

## Review by J1

I read `derived.tex` at Tag 0BK6 and checked that the item has exactly its two advertised conclusions: the termwise product is K-injective and it is the derived product. I read the full statements of `def-pur-kinjective-complex`, `lem-weil-pbc-kinjective-hom-derived`, and `def-weil-category-product`; the first supplies the null-homotopy criterion used in Step 1, the second supplies both derived-to-homotopy Hom bijections in Step 3, and the third supplies the universal product criterion. Step 2 is the direct componentwise chain-map and homotopy calculation, so it is marked elementary. The ringed-space and family hypotheses are carried unchanged through all steps. I corrected the imported dependency list by adding the product definition, and verified the singleton and empty-family edge cases.

What I could not finish:

- Nothing; the split is ready for the second reader and dry-run delivery.

## Second reading by J1

- Item statement: checked against Stacks `derived.tex`, Tag 0BK6 (`lemma-product-K-injective`), hypothesis by hypothesis; repaired the specialization to a ringed space to the source's arbitrary abelian category and restored the degreewise product-existence hypothesis.
- Step 1: checked against the Tag 0BK6 Hom-complex argument and `def-sp-kinjective-bridge`; the product Hom-complex identification and exactness argument now appear explicitly.
- Step 2: checked against the source's identification of chain maps and homotopies with component families; elementary and self-contained.
- Step 3: checked against `lem-weil-pbc-kinjective-hom-derived` and `def-weil-category-product`; the derived Hom product bijection and universal property are stated explicitly.
- Existing dependency nodes: opened both cited statements and verified that each citation supplies the fact used; no new node was needed.
- Edge cases: the empty index set gives the zero product when it exists, a singleton gives the original complex, and the proof works uniformly for both.
- Mathlib searches: rechecked the recorded grep, LeanFinder, Loogle, and LeanSearch searches; no exact product-closure declaration was found.

Changes made: corrected the item statement and dependencies to match Tag 0BK6, expanded Step 1 and Step 3, replaced short citation quotes with verbatim supporting excerpts, and corrected `created.item` to this item so delivery preflight recognizes the split.
