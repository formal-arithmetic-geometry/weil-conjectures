Files written:

- `def-sp-exact-couple.json`: definition node, no new nodes, Mathlib no-match.

Attachments: none. No sorry-free declaration in `WeilConjectures/` states this definition.

WANTED: none.

The imported item is a definition, so there is no proof to split into theorem nodes. Its statement is self-contained apart from the cited abelian-category definition `def-sp-abelian`. The source is the blueprint node `def-sp-exact-couple` and its cited Stacks Project Definitions 12.21.1 and 12.21.3 (Tags 011Q and 011S), Lemma 12.21.2 (Tag 011R), and Remark 12.21.5 (Tag 011U). I searched the project source for the item id, exact-couple names, and the Stacks tags; no declaration exists. I also searched Mathlib twice by LeanFinder, Loogle, and grep, and recorded LeanSearch as unavailable; Mathlib has spectral-object and spectral-sequence infrastructure but no exact-couple definition matching this statement.

## Review by G1

I read the imported node and the blueprint source. The statement introduces the abelian category, both bigraded objects, all three maps with their bidegrees, the three pointwise exactness conditions, the derived couple, and the recursive spectral-sequence pages. These clauses agree with the Stacks definitions and lemma cited by the source; the shift variant is represented by the stated bidegree convention. The only statement dependency is `def-sp-abelian`, which is exactly the notion used in the opening hypothesis. Since this is a definition, it has no proof steps, proof dependencies, or citation quotes; `citations.json` is therefore empty. I checked small degenerate cases conceptually (zero bigraded objects and zero structure maps satisfy the exactness equations) and made no mathematical changes to the imported statement. The blueprint reference is filled with `same_as: []`, and the Mathlib search results are recorded verbatim enough to distinguish the unrelated spectral-object framework from an exact-couple match.

What was wrong or incomplete in the imported metadata: it was still marked `imported`, had no Mathlib search record, and had an unset blueprint `same_as`; these are repaired here. No source error was found.

What could not be finished: nothing; this definition has no proof node to formalize.

## Second reading by G1

- Item statement: checked every clause against the blueprint definition and Stacks `homology.tex` Definition 12.21.1 (Tag `011Q`), Lemma 12.21.2 (Tag `011R`), Definition 12.21.3 (Tag `011S`), and the shifted-couple variant Remark 12.21.5 (local tag `0AMJ`); the bigraded indexing agrees with the project's truncation-couple convention.
- Proof steps: none; this is a definition node, so there are no proof dependencies or uncited steps to audit.
- New nodes: none; the split creates no auxiliary node, so B1-B7 and duplicate-node checks are vacuous. The Mathlib searches recorded in `searches.jsonl` were rerun and found no exact-couple declaration.
- Edge cases: zero bigraded objects and zero maps satisfy the exactness equations; the quotient description of `E'` and the recursive page construction remain meaningful in these degenerate cases.

Changes made:

- Corrected the shifted-couple source citation from the unrelated Tag `011U` (the differential-object section) to the shifted-exact-couple Remark 12.21.5, Tag `0AMJ`.
- Made `f'` explicitly induced on the quotient `E'` by writing it on a class `[x]` and identifying its value in the image object `D'`.

## Source error

The imported metadata cited Tag `011U` as the shift-functor exact-couple variant. In the local Stacks source, `011U` is the differential-object section; the relevant shifted exact-couple remark is labeled `remark-shifted-exact-couple` and carries tag `0AMJ`. The citation was corrected rather than silently retained.
