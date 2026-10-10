# Stage 1: lem-sc-local-ring-artin-schreier-kernel

## Files written

- `dag/nodes/sec-curve-estimates/lem-sc-local-ring-artin-schreier-kernel.json`: split the local-ring kernel statement into three complete steps. Its proof uses the new field leaf and the existing local-ring unit criterion.
- `dag/nodes/sec-curve-estimates/lem-sc-field-artin-schreier-kernel.json`: new statement, Mathlib leaf. `Subfield.mem_bot_iff_pow_eq_self` at `Mathlib/FieldTheory/Finite/Basic.lean:748` identifies the roots with the prime subfield; `ZMod.fieldRange_castHom_eq_bot` at line 579 identifies that subfield with the image of `ZMod p`.

## Attachments

None. The source search found no exact declaration for the item or the new field leaf, and both have `lean_audit.slopmaster2.state = none`.

## Wanted

None. Stacks `etale-cohomology.tex`, Tag 0A3J (`section-artin-schreier`), asserts the exact sequence; Stacks `algebra.tex`, Tag 00E9 (`lemma-characterize-local-ring`), supplies the local unit criterion. The missing local-ring calculation is marked agent-written.

## Corrections

For L review: the item's origin `blueprint.same_as` points to `lem-sc-artin-schreier-k`, whose statement requires an algebraically closed field and also claims surjectivity of the Artin-Schreier map. It does not appear to be the same statement as the arbitrary local-ring kernel result. The origin metadata is preserved. The blueprint and Stacks assert the kernel identification without the local-ring calculation. The proof now reduces to the residue field, obtains the unique coefficient in `F_p`, and writes out why the difference vanishes in the local ring.

## Verification and limits

`python3 tools/review_split.py lem-sc-local-ring-artin-schreier-kernel` passes. `python3 tools/check_dag.py` reports 0 cycles and 0 self-loops; its 7 reach and 11 route findings are in other nodes. No Lean was written or built. This item is not the key node of `sk-prop-h2`, whose unrelated unit realization is still unrecorded.

## Review by C1

I read the current parent node, the new field node, Stacks `etale-cohomology.tex` Section 0A3J (`section-artin-schreier`, lines 9599-9610), Stacks `algebra.tex` Lemma 00E9 (`lemma-characterize-local-ring`, lines 3366-3397), and Mathlib `FieldTheory/Finite/Basic.lean` lines 579-586 and 729-751. The Stacks section asserts the Artin-Schreier kernel as the constant `Z/p` sheaf; the local-ring statement isolates the stalk calculation needed by the parent `lem-sc-as-sequence`. Stacks does not supply that calculation, so the node correctly marks the proof as agent-written. The field leaf is precisely the residue-field case, for any field of characteristic the prime `p`; Mathlib `Subfield.mem_bot_iff_pow_eq_self` identifies the fixed points, and `ZMod.fieldRange_castHom_eq_bot` identifies the bottom subfield with the canonical image. The existing `lem-sc-artin-schreier-k` concerns algebraically closed fields and also asserts surjectivity of `x^p-x`; it does not duplicate the new leaf.

A: The sandbox contains only the changed item node, its new child, and this report. The child id does not exist in the current clone, `created.item` is this item, and the item has a `split_report`. The delivery command must check the final one-commit shape and preflight. The parent's current `lean_audit.slopmaster2.state` is `none`, as is the child's proposed audit. A read-only search of `WeilConjectures/` found no declaration tagged for either node and no exact local-ring result. The unrelated `blueprint.same_as` mismatch noted above is existing maintainer metadata; it was preserved.

B: The child introduces `p`, `K`, the characteristic assumption, the canonical map, and its solution set explicitly; it is statement only with empty `proof` and `proof_deps`. Its statement cites `def-weil-field` for the field, `def-pc-field-characteristic` for characteristic `p`, and `def-weil-finite-field-q-elements` for `F_p=Z/pZ`; I read each definition and listed all three in `stmt_deps`. Its TeX is encoded once in JSON. The Stacks citation gives tag 0A3J and the actual section label. Its Mathlib match names the declaration, file, and integer line 748, with supporting read lines 748-751, 579-581, 583-586 and 729; a prime `p` and a field `K` provide the theorem's `Fact p.Prime` and `CharP K p` hypotheses. A finite field, an infinite field, and `p=2` all satisfy the same fixed-point characterization.

C/D: Step 1 passes to `R/m`, a field, and cites the new field leaf for the unique coefficient. Step 2 uses that same leaf for `c^p=c` and the existing `lem-weil-pbc-local-ring-unit-criterion`, whose statement exactly identifies elements outside the unique maximal ideal as units (Stacks 00E9). Its intervening Frobenius binomial expansion and `b(1-b^(p-1))=0` are written in the step, so no source proof is borrowed silently. Step 3 cites the field leaf for the converse and injectivity after reduction. `proof_deps` is the union of those citations. The child is strictly smaller than the local-ring result; the steps retain the argument rather than moving the item into it. I searched current DAG nodes for the Artin-Schreier field claim: the algebraically closed-field node is broader in one direction and has a different second conclusion, so it cannot replace the new leaf. The child depends on no node and the other cited node is pre-existing, giving no new cycle or cross-unit proof route.

E: The residue field exists because `R` has a proper unique maximal ideal. The prime characteristic condition descends to it. In step 2, `b` lies in `m`; since `p>=2`, `b^(p-1)` lies there and `1-b^(p-1)` is outside it, hence is a unit. This works also for nonreduced local rings: no reducedness or Henselian assumption is used. The canonical `F_p` map into a field is injective, including in characteristic two, which supplies step 3's uniqueness. No extra hypothesis is introduced. The delivery preflight first identified missing definition citations and a missing numeric Mathlib line in the new leaf; I corrected both in the sandbox, leaving the proof steps unchanged. The existing `same_as` metadata discrepancy is reported above for L rather than changed here.
