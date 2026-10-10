# lem-weil-pbc-graded-finiteness-cohomology

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-graded-finiteness-cohomology.json`: split Stacks 0897(1) in five steps; statement unchanged.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-qcqs-cohomology-direct-sum.json`: new unsplit 01FF node, no Mathlib match after LeanSearch, LeanFinder, Loogle and source grep.

## Source and proof

Read Cohomology of Schemes Lemma 0897, `coherent.tex` lines 5247-5300, in `/home/ubuntu/weil-conjectures-sheaf-F2/literature/stacks-project/` (the literature copy is absent in this H1 checkout). Its part (1) has exactly the item's hypotheses: Noetherian A, finite type graded A-algebra B, proper X over Spec A, and finite type quasi-coherent graded module. The item's local homogeneous-generator condition is the explicit finite-type interpretation. Stacks' proof first forms X' = X times_Spec(A) Spec(B), obtains properness by 01W4, B Noetherian by 00FN, X' Noetherian by 01T6, identifies X' as relative Spec(f^* B~) by 01LX, applies 01SB to the module, makes it coherent using 01XZ, identifies cohomology by 089W, and concludes by 02O6. The five steps cite nodes for these facts and write out the B-linearity and graded convolution formula.

The source omits the finite-type verification for the corresponding module on X'. The existing `lem-weil-pbc-affine-module-finite-type` states precisely that fact under the affine equivalence; step 3 checks its hypotheses. The additional direct-sum comparison H^p(X, (+)_m G_m) = (+)_m H^p(X,G_m) is not part of 089W or 02O6, so the new node isolates it from Cohomology Lemma 01FF, `cohomology.tex` lines 3194-3225. Its hypotheses hold because proper X over affine Spec A is quasi-compact and quasi-separated. Finite partial sums form a directed system, and finite direct sums commute with additive cohomology. The new node is strictly smaller than 0897 and does not itself assert finite generation.

Checked edge cases: B=A concentrated in degree zero gives a finite type graded module with only finitely many nonzero generating degrees, hence the finite B-module conclusion is consistent; p=0 gives global sections and the same affine/proper argument; X empty gives zero modules; infinitely many nonzero pieces are allowed because 01FF handles arbitrary direct sums. The finite type over A condition on B is needed for Noetherianity of B. The source's 0897(2) ample-vanishing clause is outside this item and is not asserted here.

## Blueprint and DAG searches

`tools/blueprint_refs.py ancestor lem-weil-pbc-graded-finiteness-cohomology` gives `thm-weil-pbc-finite-etale-lifting`. Searches of all imported blueprint nodes for `graded finiteness`, `finite graded`, `cohomology graded`, and `direct sums cohomology` found no node stating 0897(1) or the 01FF specialization; `same_as` is `[]` on both nodes. The item's `from.place` already identifies step 7 of that ancestor through the formal-functions/Rees-finiteness chain. Its split report names the route. Existing DAG searches by tags 01W4, 00FN, 01T6, 01LX, 01SB, 01XZ, 089W, 02O6 found the nodes cited in steps 1, 3 and 4. No new duplicate node was made for any of them.

`lem-pc-coherent-hi` (02O6 clause, unit `sk-thm-picard-rr`) is a generic proper-coherent-cohomology tool used as a black box; the lead must decide `tool_uses`. `pqf-lem-coherent-ft-locnoeth` (01XZ, unit in sec-abelian-varieties) is likewise the existing generic equivalence, not a replacement for a unit step. Other non-leaf dependencies cited are in the item's unit `sk-thm-p1`.

## Attachments and wanted sources

No Lean declarations to attach (`lean_audit.slopmaster2.state = none`). No source is wanted: the required Stacks TeX is available in the sibling checkout, though not materialized under H1 `literature/`.

## Open work

The new 01FF node remains unsplit. No Lean was written or built. The lead should review the two generic tool uses and the source correspondence.

## Review by H1

I read Stacks Cohomology of Schemes 0897(1) in `coherent.tex` and Cohomology 01FF in `cohomology.tex`. The item's written-out homogeneous action and local generator condition give the same graded algebra/module hypotheses as 0897. Step 1 invokes the proper base-change, Noetherian finite-type and finite-type-source statements it cites; steps 2 and 3 reconstruct the graded module on the relative spectrum and use the cited affine-module correspondence and finite-type node, which supplies the details omitted in 0897; step 4 uses the 02O6 clause of `lem-pc-coherent-hi` and the affine cohomology edge map; step 5 uses the new 01FF specialization and checks the displayed $B$-action on each graded piece. I checked the statements of those cited nodes, including the natural edge map. The new 01FF node has its own qcqs and arbitrary-family hypotheses, no proof steps, all three Mathlib search types with no match, and a specific blueprint ancestor; finite sums and an empty family test its direct-sum claim. I searched the existing DAG and blueprint for 01FF and graded cohomology duplicates. I recorded `lem-pc-coherent-hi` and `pqf-lem-coherent-ft-locnoeth` as generic black-box tools from other units: neither replaces a unit proof step. I sent nothing back to the worker.
