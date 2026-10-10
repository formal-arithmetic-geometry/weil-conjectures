Files written:

- `dag/nodes/sec-abelian-varieties/lem-sp-half-plane-graded-canonical.json` (statement, split; no new nodes; Mathlib searches found no match).

Attachments: none.

WANTED: none.

The item had no Lean declaration in `weil-src-slopmaster2`. I kept its statement and filled the proof from the stabilized-page argument referenced by `lem-sp-couple-morphism`. No child node was created: the proof uses the existing half-plane convergence theorem, exact-couple definition, and the existing derived-couple exactness statement. The latter is outside this unit and is recorded as a tool use because it supplies the iterated-page exactness and the formula for `D_r`.

## Review by F1

I read `dag/nodes/sec-abelian-varieties/thm-sp-half-plane-convergence.json`, `def-sp-exact-couple`, `def-sp-convergence`, and `dag/nodes/sec-proper-base-change/lem-sp-derived-couple-exact.json`, together with the source references Tags 011T and 012F in `literature/stacks-project/homology.tex` as named by the item. Step 1 uses the half-plane stabilization bound, the exact-couple page recursion, and the derived-couple statement that `D_r` is the image of the indicated power of `alpha`; these statements supply the stabilized quotient and the filtration quotient. Step 2 uses the derived-couple page maps and the convergence definition's canonical map from `g`, then checks that the `alpha^p` map is the corresponding filtration quotient map; both are quotient maps from the same `G_q/G_{q-1}` object. Step 3 uses the convergence definition's criterion that two epimorphisms with the same kernel induce the canonical isomorphism. I verified the hypotheses `p >= 0`, `q >= a`, `r > max(q-a+1,p)`, and `u <= 0` at the stabilized-page choice, and checked the edge case `p=0` where `alpha^p` is the identity. The Mathlib searches were rerun for the item with LeanFinder, Loogle, grep, and LeanSearch; no exact-couple declaration was found, and LeanSearch was unavailable.

## Second reading by F1

- Item statement: checked against the half-plane convergence and convergence-definition statements and Stacks Tags 011T and 012F; the hypotheses and the assertion that the canonical comparison is induced by `g` and `alpha^p` are retained.
- Step 1: checked against `thm-sp-half-plane-convergence`, `def-sp-exact-couple`, and `lem-sp-derived-couple-exact`; the stabilization bound, iterated image formula, exact sequence, and filtration indices agree. Repaired the previously implicit `alpha^{-u}` isomorphism by spelling out the two vanishing neighboring terms and exactness.
- Step 2: checked against `lem-sp-derived-couple-exact`, `def-sp-convergence`, and the filtration formula in `thm-sp-half-plane-convergence`; the iterated `g_r` formula and the two quotient maps have the same source quotient and kernel.
- Step 3: checked against `def-sp-convergence`; its same-kernel quotient criterion exactly gives the claimed canonical isomorphism, and the step is elementary from that definition.
- New nodes: none; there were no child nodes to audit. Existing-node searches found the cited exact-couple and convergence statements, and Mathlib searches recorded in the item found no exact-couple or `E_infty` declaration.
- Edge cases checked: `p=0` makes `alpha^p` the identity; `q=a` still permits the stated stabilization bound; the zero/vanishing case gives zero source and zero quotient; the field and trivial exact-couple cases reduce to the same quotient criterion.
- Changes: expanded Step 1's exactness argument for `alpha^{-u}`; appended this second-reading record. No statement, citation quote, or dependency was otherwise changed.
