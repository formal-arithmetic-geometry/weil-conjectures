Files written:
- `lem-sp-derived-couple-functoriality.json`: statement node, split with three proof steps; no new nodes.
- `citations.json`: six verbatim step-to-node citations.

Attachments: none.

WANTED: none.

The item was not already implemented in the Lean source: grep of `WeilConjectures/` found no declaration or blueprint tag for it. The existing node `lem-sp-couple-morphism` depends on this item, so it cannot serve as a citation. The item statement and its hypotheses were retained. The imported proof was empty; I supplied the missing argument rather than creating a node that merely restates one clause of the item. The exactness theorem `lem-sp-derived-couple-exact` is outside this unit, so it is declared as a generic tool use in `split_report.tool_uses`.

## Review by K1

I read the source references in Stacks `spectral-sequences.tex`, Definitions 12.21.1 and 12.21.3 and Lemmas 12.21.2 and 12.21.4 (Tags 011Q, 011S, 011R, 011T), together with the statements of `def-sp-exact-couple`, `lem-sp-derived-couple-exact`, and `def-sp-convergence`. The item statement agrees with the source's morphism-of-couples construction, including preservation of bidegrees, the three commutative squares, all derived pages, and the limiting quotient.

Step 1 uses exactly the derived-couple formulas and the existence/uniqueness clause in `lem-sp-derived-couple-exact`: the equality `t_E d = d' t_E` sends kernels to kernels and images to images, so the quotient map exists; `t_D` similarly sends the image of alpha to the target image, and the defining restriction/factorization identities descend. The quoted clauses explicitly state the derived maps exist and are unique. Step 2 uses the iteration clause of `lem-sp-derived-couple-exact` and the page recursion in `def-sp-exact-couple`; induction gives the page maps and differential compatibility by composition. Step 3 uses the recursive definitions of cycles and boundaries and the limiting quotient in `def-sp-convergence`, together with the exactness of every iterated couple; induction on the page number proves preservation of `Z_r` and `B_r`, and inclusion of the limiting intersection/union gives the induced map at infinity.

I checked the hypotheses at each use: both couples are in one abelian category, the three structure maps preserve their stated bidegrees and commute, and the target iterates are defined because the derived-couple exactness theorem applies at every type. I tested the construction in the degenerate case `d=0`, where the derived E-term is the original E-term and the induced map is simply `t_E`, and in the zero couple, where all kernels, images, cycles, and boundaries are zero. The Mathlib searches for the item were run with LeanFinder, Loogle, grep, and LeanSearch; LeanFinder returned only unrelated homology-sequence maps, Loogle and grep found no exact-couple declaration, and LeanSearch was unavailable. No statement was found in the Lean source, so there is no attachment.

What could not be finished: no Lean proof was attempted, as required for stage 1; this stage produces only the natural-language DAG artifact.

## Second reading by K1

- Step 1 checked against the derived-couple formulas and functoriality clauses in Stacks Tags 011Q and 011R, and against the statements of \`def-sp-exact-couple\` and \`lem-sp-derived-couple-exact\`; verdict: valid kernel/image transport and descended structure maps, with ambiguous derived-term wording repaired.
- Step 2 checked against Stacks Tags 011S and 011R and the recursive page clause of \`def-sp-exact-couple\`; verdict: valid induction over type-\(r-2\) couples and differential compatibility.
- Step 3 checked against the cycle/boundary recursion in \`def-sp-convergence\` and the iteration statement of \`lem-sp-derived-couple-exact\`; verdict: valid preservation of cycles and boundaries and induced limiting quotient map.
- No new nodes were introduced; therefore B1-B7 and new-node duplicate/Mathlib checks are vacuous. Existing cited nodes were opened and their quoted statements verified verbatim in \`citations.json\`.
- Small cases checked: the zero couple and the case \(d=0\) give the zero map and the original \(t_E\), respectively; the bidegree hypotheses and all three commutative squares are used at the indicated steps.
- Changed Step 1 wording to distinguish the source derived \(E\)-term from the target derived \(E'\)-term and to name the induced derived \(D\)-term map explicitly; no mathematical statement was changed.
