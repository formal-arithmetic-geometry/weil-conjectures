1. Files written:

- `dag/nodes/sec-smooth-purity/lem-weil-pbc-irreducible-lisse-strata.json` — statement split into two proof steps; no new nodes; Mathlib search found only the existing finite-components generalization.
- `citations.json` — verbatim citations for every node used by each step.

2. Attachments: none.

3. WANTED: none.

4. The imported item was marked `imported` and had an uncited second proof paragraph. I changed it to `split`, filled the blueprint reference, cited the constructibility and scheme-convention definitions, and retained the existing `lem-weil-pbc-noetherian-finite-components` Mathlib leaf. No statement change was needed.

5. Nothing remains unfinished.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## Review by C1


I read the item node, the `sk-prop-sf-cbc` unit record, the Smooth Purity chapter record, and the definition nodes `def-weil-pbc-etale-sheaves` and `def-weil-pbc-scheme-conventions`. I also read the existing `lem-weil-pbc-noetherian-finite-components` node; its statement is exactly the finite irreducible-components fact used in step 1 and it is a Mathlib leaf. Step 1 takes the finite lisse partition directly from the constructibility clause and then applies that leaf to each Noetherian stratum. Step 2 uses only the definition of finite locally constant/lisse sheaf and the locally closed convention: an irreducible component minus finitely many other closed components is a nonempty open irreducible subset, the resulting subsets are disjoint and cover the stratum, and restricting an etale trivialization preserves local constancy and finite stalks. I verified that the hypotheses are sufficient for every component and that the finite original partition makes the final family finite. I ran LeanFinder, Loogle, grep, and LeanSearch through `msearch.py`; the first found only the existing finite-components theorem, Loogle and grep found no exact sheaf theorem, and LeanSearch was recorded unavailable. The citation quotes were copied verbatim from the cited node statements.
## Second reading by C1

- Item statement: checked against the imported blueprint node and the constructible/lisse definitions; the Noetherian, finite-partition, irreducibility, locally closed, and finite-stalk clauses agree hypothesis by hypothesis.
- Step 1: checked against `def-weil-pbc-etale-sheaves` and `lem-weil-pbc-noetherian-finite-components`; the refinement by the finitely many irreducible components is explicit.
- Step 2: checked against `def-weil-pbc-scheme-conventions` and `def-weil-pbc-etale-sheaves`; the component topology, disjoint cover, reduced subscheme choice, and restriction of lisse trivializations are stated explicitly.
- New nodes: none; duplicate and Mathlib searches were rechecked, with only the existing finite-components Mathlib leaf matching.
- Edge cases checked: the empty scheme has the empty partition; a one-point field has one irreducible stratum; a one-stratum lisse sheaf remains unchanged; every nonempty Noetherian part has at least one component, so the indexing is defined.

Changes made: removed the unrelated affine citation from step 1; expanded both proof steps to state the component refinement and irreducibility argument; replaced the loose locally closed citation with the verbatim subscheme-convention statement; added this second-reading record.
