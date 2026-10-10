1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-torsor-h1-ext-pushout.json`: item split into three proof steps; no new nodes.

2. Attachments: none.

3. WANTED: `literature/stacks-project/cohomology.tex`, Lemma 02FQ, for the pushout-extension and fibre-over-one construction. The repository contains the citation indexes but not the Stacks source file.

4. What was checked and changed: the item has no declaration tagged `lem-sc-torsor-h1-ext-pushout` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, and the existing Lean torsor declarations do not state this quotient pushout result. I searched the whole DAG and blueprint for pushout-extension and contracted-product statements; the only directly reusable result is `lem-weil-pbc-pushout-short-exact-sequence`, whose statement explicitly gives exactness after an abelian pushout. Step 1 uses precisely that statement after spelling out the quotient's pushout universal property. Step 2 checks sections of the fibre over 1 and verifies that the quotient relation is exactly the contracted-product relation. Step 3 checks local nonemptiness and unique differences in the kernel, so the fibre is a torsor. The generic pushout node is declared as an off-unit tool in `split_report.tool_uses`; no cycle through `lem-sc-torsor-h1-functoriality` is introduced.

## Review by K1

I read the item statement and its source citation (Stacks 02FQ) and compared every hypothesis: scheme, Zariski abelian sheaves, morphism of coefficients, short exact extension, constant integer sheaf, quotient pushout, and fibre over 1. I opened the cited generic pushout node and verified that its statement supplies exactly the short exact sequence and induced projection needed in Step 1. The quotient universal-property argument identifies the displayed quotient with that pushout. Steps 2 and 3 are definition-level checks: the relation on pairs is the stated contracted-product action, and the fibre of an exact sequence over a section is locally inhabited with unique differences in the kernel. I tested the calculation in the identity case `G = G'`, `varphi = id` (recovering `E` and `T`) and in the zero-coefficient case (the quotient relation and fibre action behave as expected). No new statement-only node was required, and no Mathlib declaration states the result.
