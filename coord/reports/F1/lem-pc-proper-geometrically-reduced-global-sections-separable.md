1. Files written

- `dag/nodes/sec-picard-framework/lem-pc-proper-geometrically-reduced-global-sections-separable.json`: item repaired; four proof steps; Mathlib searches found no exact theorem.
- `dag/nodes/sec-picard-framework/lem-pc-finite-extension-tensor-algebraic-closure-reduced-separable.json`: statement-only field-theory node; Mathlib searches found no exact theorem.
- `citations.json`: citations for every non-elementary dependency in every step.

2. Attachments

None.

3. WANTED

None. The Stacks source was read from `/home/ubuntu/c1-stacks-review/varieties.tex`, Lemma 0BUG (`lemma-proper-geometrically-reduced-global-sections`), lines 1933-1988. The field-theory source is Stacks Algebra Tags 030W and 030V.

4. Repairs and checks

The returned product node was deleted because it moved the whole content of the item into a stronger, non-smaller statement. The item now follows the proof of 0BUG: (1) finite-dimensional global sections using `lem-pc-euler-characteristic-well-defined` with `F=O_X`, `i=0`; (2) the flat base-change isomorphism using `lem-weil-pbc-flat-base-change-global-sections-qcqs`, with flatness of `Spec(kbar) -> Spec(k)` and QCQS verified from properness over affine; (3) reducedness of global sections of the reduced base change, checked stalkwise; and (4) the finite-extension criterion from Tags 030W/030V. I searched the DAG and blueprint before adding the new criterion node and found no existing statement with that converse. Its statement has the exact hypotheses `K/k` finite and `K tensor_k kbar` reduced, and its source is recorded as Tags 030W/030V.

## Review by F1

I read the complete Stacks proof of Lemma 0BUG in `varieties.tex` lines 1933-1988, including the finite-dimensionality argument, the product-of-fields argument, and the final geometric-reducedness/separability paragraph. I also read the statements of every node cited by each item step. Step 1 uses the cited Euler-characteristic node exactly for finite-dimensionality of `H^0`; the properness hypothesis supplies its applicability. Step 2 uses the algebraic-closure existence node, the algebraic-closure and flat-morphism definitions, proper-implies-QCQS over an affine base, and the exact global-sections flat-base-change isomorphism. Step 3 uses the geometric-reduced definition and the reduced-scheme definition; the stalk argument shows a nilpotent global section vanishes. Step 4 uses only the new finite-extension criterion, whose statement exactly supplies the conclusion from the hypotheses established in steps 1 and 3. I checked the finite one-factor case and `X = Spec(k)` as small cases. The previous product helper and its invalid citation were removed, and all citations were rewritten to quote statements in the current DAG.

5. Unfinished

None.
