# Stage-1 worker report: def-weil-pbc-rational-category

1. Files written: `dag/nodes/sec-proper-base-change/def-weil-pbc-rational-category.json` (definition; Mathlib searches found no exact category-level match). No new nodes.
2. Attachments: no exact Lean declaration attachment.
3. WANTED: none.
4. The imported node had no blueprint provenance fields filled and was still `imported`; I filled its blueprint ancestor/place and marked it `split`. I retained the Karoubi-envelope dependency because the statement explicitly says that no Karoubi envelope is taken, and added the existing generic scalar-localization and uniformizer-localization nodes needed to identify the construction and the equality `O_E[1/varpi] = E`. The source blueprint's definition is a specialization of the already split generic `def-weil-rationalization-karoubi`; no separate proof steps or new nodes are appropriate for a definition.
5. Nothing remains unfinished.

## Review by NJ

I read the item source `literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/def-weil-pbc-rational-category.md` (node order 1305), the unit record `sk-thm-properbasechange`, and the chapter record. I also searched both source trees for the blueprint tag and for rational-category declarations. The source states exactly the finite extension E/Q_l, valuation ring, uniformizer, same-object raw scalar localization, Hom tensor formula, and explicit absence of Karoubi completion; no exact sorry-free declaration exists under `WeilConjectures/`. I opened the existing nodes `def-weil-pbc-bounded-constructible-complete`, `def-weil-karoubi-envelope`, `def-weil-linear-scalar-localization`, and `lem-weil-l-adic-integers-localization-uniformizer` and verified that each supplies the corresponding notion named in the item. The generic node `def-weil-rationalization-karoubi` carries the same raw-localization construction, while the current item specializes its integral category to the proper-base-change category. I ran LeanFinder, Loogle, Mathlib grep, and LeanSearch searches; the first three returned no exact category-level declaration and LeanSearch was unavailable, recorded as such. As this is a definition, there are no proof steps or citation quotes; `citations.json` is therefore empty. I checked edge cases conceptually (the raw localization keeps exactly the integral objects and inverts only powers of the chosen uniformizer), and made no statement weakening or hypothesis changes.

## Second reading by NJ

- Item statement: checked the finite extension, valuation ring, uniformizer, raw localization, same-object clause, Hom tensor formula, and explicit absence of Karoubi completion against the blueprint node `def-weil-pbc-rational-category` (order 1305); verdict: retained, with the previously implicit scheme variable `T` made self-contained as a noetherian finite-dimensional scheme in the proper-base-change setting.
- New nodes: none; consequently there are no proof steps or new-node statements to audit. The item is a definition and its proof field remains empty.
- Existing dependencies: opened `def-weil-pbc-bounded-constructible-complete` for the integral category, `def-weil-linear-scalar-localization` for same objects and Hom tensor localization, `lem-weil-l-adic-integers-localization-uniformizer` for `O_E[1/varpi]=E`, and `def-weil-karoubi-envelope` for the explicitly excluded completion; each supplies the notion used.
- Blueprint and duplicate search: ran `tools/blueprint_refs.py search` over the imported blueprint; the only same construction is the generic `def-weil-rationalization-karoubi`, which is a broader construction and does not replace this proper-base-change specialization.
- Edge cases: the raw localization preserves the zero object and all integral objects, and for a field coefficient (`E=Q_l`, `varpi=ell`) gives the stated localization; no empty-scheme or object-index restriction is introduced.

Changes made: added the missing self-contained hypothesis introducing `T`; added the scalar-localization and uniformizer-localization dependencies so every non-elementary notion in the statement is cited. No proof steps or new nodes were created.
