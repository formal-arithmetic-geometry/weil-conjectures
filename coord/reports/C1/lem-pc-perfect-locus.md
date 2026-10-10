Files written:

- `dag/nodes/sec-picard-framework/lem-pc-perfect-locus.json`: item split into four proof steps; no new nodes.
- `citations.json`: verbatim citations for every node used by every step.

Attachments:

- None. The corresponding slopmaster2 declaration remains transitively sorry-dependent.

WANTED:

- None.

What was wrong in the imported item:

- The imported proof cited only `def-pc-perfect-complex` while using a substantial cancellation argument and a field-extension dimension argument. I replaced the first with the existing Stacks Tag 00MT node `lem-weil-pbc-free-complex-unit-entry-splits` and the second with the existing Mathlib leaf `lem-pc-finrank-field-base-change`.
- No new node was created: a whole-DAG search found the exact cancellation lemma and the exact scalar-extension dimension lemma already present.

## Review by C1

I read the item source in the blueprint file `literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-perfect/lem-pc-perfect-locus.md`, the unit route in `dag/units/sk-thm-picard-perfect.json`, the definition node `def-pc-perfect-complex`, the existing Tag 00MT node `lem-weil-pbc-free-complex-unit-entry-splits`, and the Mathlib leaf `lem-pc-finrank-field-base-change`. Step 1 now takes exactly the local finite-free model from the perfect-complex definition and the contractible-summand cancellation stated by Tag 00MT. Step 2 uses the scalar-extension dimension statement to identify the rank of the residual degree- $i$ term; the remaining residue-field and localization manipulations are elementary from the displayed complex. Step 3 is the open-neighbourhood and overlap construction directly from Step 2. Step 4 uses the derived-fibre base-change identity and the cited dimension formula; faithful flatness of a field extension and containment in an open subscheme are elementary here. I checked the small cases $r<0$ (empty locus), a one-term complex (the locus is all of the base when its rank is $r$), and a contractible two-term identity complex (the residual locus is empty for every degree). The blueprint reference was filled with the exact proof paragraphs realized by these four steps, and the cross-unit Tag 00MT lemma is declared as a tool use.

## Second reading by C1

- Item statement: checked against the blueprint item and its definition dependencies; the universal open-locus characterization and integer parameters agree hypothesis by hypothesis.
- Step 1: checked against `def-pc-perfect-complex` and the full statement of `lem-weil-pbc-free-complex-unit-entry-splits`; the finite cancellation and termination argument use exactly those statements.
- Step 2: checked on the residue-field complex and `lem-pc-finrank-field-base-change`; zero differential implies fibre cohomology equals the graded terms, and the localization of finitely many basis operations is explicit.
- Step 3: checked against Step 2 and the definition of the locus; the neighbourhood argument gives openness and the overlap identification through $H^i$.
- Step 4: checked the derived-fibre identity against `def-pc-derived-pullback` and the dimension preservation against `lem-pc-finrank-field-base-change`; faithful flatness and open-subscheme factorisation are elementary here.
- Existing dependency `lem-weil-pbc-free-complex-unit-entry-splits`: searched the whole DAG and retained the exact Tag 00MT node; no duplicate was created.
- Existing dependency `lem-pc-finrank-field-base-change`: searched the whole DAG and retained the exact Mathlib leaf; no duplicate was created.
- Small cases checked: negative rank (empty locus), one-term complex (whole base at matching rank), and a contractible identity complex (empty locus).

Changes made: restored the imported node's required `blueprint.from = null` shape, recorded the unit realization for `sk-thm-picard-perfect`, cited `def-pc-derived-pullback` for the derived-fibre formula, and added its verbatim citation quote.
