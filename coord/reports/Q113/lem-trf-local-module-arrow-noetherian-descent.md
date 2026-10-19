# Delivery report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-local-module-arrow-noetherian-descent.json` — the split item, a statement with four proof steps and no new child nodes.
- `citations.json` — verbatim statement excerpts for every cited node in every step.

Attachments: none. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states this item; searches for the item id, the 046Y name, and the local module-arrow terminology found no declaration.

WANTED: none.

No statement error was found. The source's simultaneous approximation paragraph is expanded using the existing directed Noetherian tower theorem and the finite-presentation module/map descent theorem. The stage rings are obtained from the top ring of the tower with the second copy of `S`; essential finite type composes, and the Noetherian finite-type-to-finite-presentation result supplies the item's finitely presented localization description. The second module and the arrow are descended at a later affine stage, then all data are restricted to one common directed tail.

There are no new nodes. The existing algebraic nodes used below this item are generic tools from the proper-base-change unit; they are listed in `split_report.tool_uses` because the current item belongs to `sk-i-curve-zero`.

## Review by Q113

I read the item node, its parent `lem-trf-valuation-general-mod-injective`, the `sk-i-curve-zero` unit and `sec-trace-formula` chapter, and the source passages for Stacks Tags 046Y, 00QX, 00R7 and Limits Tag 01ZR. I also read the full statements of every cited node: the 00R7 tower theorem supplies local stage rings, essential finite type, colimits, and localization/base-change formulas; the Noetherian finite-type and localization nodes supply the stage Noetherian hypotheses; the finite-presentation node converts finite type over a Noetherian ring to finite presentation; and 01ZR supplies descent of a finitely presented module and a morphism after passing to a later affine stage.

Step 1 uses the tower's clauses (2), (4), and (5), then checks composition of essential finite type and the Noetherian hypotheses before applying the cited 00FN/00FP consequences. Step 2 verifies that the affine spectra of the stage rings form the inverse system required by 01ZR and that its module and morphism clauses are applied only after the module base-change identifications have been fixed. Step 3 checks the common-tail restriction, finality, pure-tensor formulas, semilinearity, and compatibility with `u`; the cited tail-colimit statement supplies preservation of the colimits. Step 4 checks that both stage modules have finite presentations, that the transition and limit comparisons carry `u_i` to `u_j` and `u`, and that the zero-module and zero-map cases are included.

I searched the whole DAG and both blueprint snapshots for the item, 046Y, simultaneous module-arrow descent, and 01ZR before changing the split; no duplicate statement was found. I retained the item's exact statement and existing Mathlib search records. No Lean files, compilers, Lake, or build tools were used.
