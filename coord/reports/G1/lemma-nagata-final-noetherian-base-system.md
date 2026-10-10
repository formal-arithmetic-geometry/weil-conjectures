# Stage 1 report

1. Files written:

   - `dag/nodes/sec-nagata-compactification/lemma-nagata-final-noetherian-base-system.json`: existing item updated to status `split`; no new nodes.
   - `citations.json`: verbatim statements used by proof step 1.
   - `report.md`: this report.

2. Attachments: none. No declaration in `WeilConjectures/` carries the item blueprint tag or states this item exactly.

3. WANTED: none.

4. The imported proof cited only `prop-nagata-noetherian-inverse-system`, but that node's statement gives finite type, affine transitions, and the limit comparison without literally spelling out Noetherianity. I repaired the proof step to cite `def-nagata-noetherian-inverse-system` as well, whose statement explicitly says each stage is Noetherian. The item is otherwise a direct application of the existing proposition, so creating a new node would duplicate a clause already present in the DAG.

5. Nothing remains unfinished.

## Review by G1

I read the item source path recorded in the node and the full statements of `def-nagata-final-noetherian-base-system`, `def-nagata-noetherian-inverse-system`, and `prop-nagata-noetherian-inverse-system`. The definition dependency introduces the selected system `N_f = N(S)` and its comparison map. The approximation-definition statement supplies that every stage is Noetherian and of finite type over `Z`, and that all transition morphisms are affine; the proposition supplies the same finite-type and affine properties for the constructed system and says that `kappa_S` identifies `S` with the inverse limit. Thus step 1 uses exactly those two statements under the selected-system identification, with no hidden hypothesis or construction.

I checked the whole DAG for duplicates by searching the two relevant node ids and the phrases “Noetherian approximation”, “finite type over Z”, “affine transition”, and “limit comparison”; the cited definition and proposition are the existing nodes that provide the needed clauses. The blueprint search found only this item. The two Mathlib-search phrasings (LeanFinder and Loogle) returned only general Noetherian scheme facts or no result for the project-specific approximation system; the Mathlib grep searches returned no matching declaration. Since the item is a project-specific restatement of existing DAG material, no Mathlib leaf or new node is appropriate. Small cases such as an affine finite-type `Z`-scheme satisfy the stated Noetherian and affine-transition clauses directly, and no additional assumptions were introduced.

## Second reading by G1

- Item statement: checked against blueprint node `lemma-nagata-final-noetherian-base-system` (order 372) and the selected-system definition; the three clauses and their hypotheses agree.
- Step 1: checked against the full statements of `prop-nagata-noetherian-inverse-system` and `def-nagata-noetherian-inverse-system`; the proposition supplies finite type, affine transitions, and the limit comparison, while the definition supplies Noetherianity. No uncited non-elementary fact is used.
- New nodes: none; therefore B1-B7, duplicate search, and Mathlib-leaf classification introduce no additional node. The repository-wide search confirms the two cited nodes are the existing sources for these clauses.
- Edge cases: the assertion specializes consistently to the empty scheme, a field viewed as an affine scheme, and an affine finite-type `Spec(A)`; no parameter `n` occurs in this item.
- Blueprint search: `tools/blueprint_refs.py search lemma-nagata-final-noetherian-base-system` finds only the item itself, so no blueprint node was omitted or duplicated.
- Changes: none to the item node, citations, or search log; this section records the independent second reading required by the delivery contract.
