# Stage-1 report: lem-trf-compact-support-system-evaluation-coherence

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-compact-support-system-evaluation-coherence.json`: repaired ordinary system-level statement and six proof steps; no new node.
- `citations.json`: eight step/node records, each quoting the complete statement used.
- `searches.jsonl`: the prescribed searches, including the nine searches rerun after the statement repair.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree for the item id, its blueprint tag, ordinary semilinear systems, and the total derived direct image. No sorry-free project declaration states this repaired item. The upstream master remains reference material only.

## WANTED

None. The repaired proof uses the existing ordinary semilinear-system node and the existing exact-functor derived-factorization node.

## What was wrong and what changed

The returned statement referred to section models, a strictification equivalence, and operations whose definitions had been removed from the current `lem-coef-semilinear-derived-sections` record. Its proof consequently cited five dropped machinery nodes and attributed unsupported content to the semilinear node. I replaced the statement with the ordinary route: the total right derived levelwise direct image after exact extension by zero, its canonical level evaluations, the induced coefficient-transition maps, and the resulting whole-tower map. The six steps now use only the ordinary system statements that exist in the current DAG. No hypothesis was added to the mathematical setup, and no target statement was weakened.

The downstream realization record that still mentions the removed model comparison must use the ordinary semilinear-system statement directly at its two citations; this delivery does not copy or alter that other node.

## Mathlib searches

After the repair I reran LeanFinder, LeanSearch, Loogle, and Mathlib-source grep searches with the repaired item id. The semantic searches returned generic derived-category, inverse-system, or complex declarations; the grep searches returned no relevant ordinary semilinear-system evaluation theorem. None states the repaired whole-tower comparison, so the item has no Mathlib match.

## Not duplicates

No new nodes were created. The existing `lem-coef-semilinear-derived-sections` node gives the component evaluation, open-adjunction, and mate clauses used here; this item combines those clauses for the specific composite (S_p^{\mathrm{str}}J_j^{\mathrm{str}}) and its whole-tower restriction.

## Review by NI

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, and delivery-errors B–E. I read the current item, the current `lem-coef-semilinear-derived-sections` statement, `def-coef-ringed-sequence-site`, and `lem-weil-pbc-exact-functor-derived-factorization`. I also read the cited blueprint source `literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-d-weil/prop-trf-rational-frobenius-integral-model.proof.md`, clause (3), and the ancestor proof record. That source requires the levelwise compact-support maps to be assembled before the derived limit; it does not define a separate comparison of models.

For step 1, `def-coef-ringed-sequence-site` says that module sheaves on the ringed sequence site realize strict quotient-semilinear systems, with actual vertical evaluations, while `lem-coef-semilinear-derived-sections` supplies the ordinary derived category and componentwise exactness. These are exactly the objects named in the repaired statement.

For step 2, I checked that `lem-coef-semilinear-derived-sections` states (V=u^{-1}_\bullet\), (G=Ru_{*,\bullet}), the adjunction, and the natural identifications (e_nG\cong Ru_{*,n}e_n), including the transition mate (b_{m,n}). Thus the step takes precisely the direct-image evaluation and coefficient-transition data that the node states.

For step 3, the same node explicitly states the ordinary open extension-by-zero/restriction adjunction on systems. Its exactness gives the levelwise (e_nJ_j^{\mathrm{str}}=j_!e_n) identification and the component units and counits. Combining it with step 2 yields the displayed (Rp_{*,n}j_!e_nM) component.

For step 4, I checked that the semilinear node states compatibility of its direct-image evaluations with transition maps and with the mate construction. Naturality of the open-extension maps then gives the displayed tower transitions; no claim about a fiberwise resolution is used.

For step 5, `def-coef-ringed-sequence-site` states that (U_Y) is exact restriction of scalars on the whole system. `lem-weil-pbc-exact-functor-derived-factorization` states that an exact functor induces the derived functor by termwise application and carries the representing maps to the derived category. This supplies the whole-tower isomorphism and its naturality.

For step 6, I checked that the semilinear node explicitly includes the units, counits, transition maps, and mate-pasting identities for both the direct-image and open adjunctions. Therefore the component formulas are carried by the canonical evaluation map; the assertion is made before any inverse limit.

I checked hypotheses at each use: the sites are small as required by the system nodes; (p) is only a morphism and (j) only an open immersion; no properness, coefficient flatness, normalization, boundedness, or K-injectivity of evaluations is assumed. The cases (M=0), (j=\mathrm{id}), and (p=\mathrm{id}) reduce to zero or identity maps. A system with a zero transition and the nonflat quotient (R/\varpi^{n+1}\twoheadrightarrow R/\varpi^n) are allowed by the cited componentwise statements and produce the stated mate transitions. No long step hides a separate lemma.

This repair addresses the return: all references to undefined section operations and the five dropped machinery nodes were removed, and the proof now follows the ordinary route stated by the current DAG.

## Unfinished work

None in this stage-1 split. The required dry run is the remaining validation step.
