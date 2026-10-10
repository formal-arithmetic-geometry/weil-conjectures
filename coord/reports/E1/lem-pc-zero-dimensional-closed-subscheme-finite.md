1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-zero-dimensional-closed-subscheme-finite.json`: statement node, split; no new node.
- `citations.json`: four verbatim statement quotes for the three proof steps.

2. Attachments:

- `lem-pc-algebraic-dim-zero-affine-finite` is the existing algebraic Tag 06LH conclusion used in step 2.
- `lem-weil-pbc-finite-over-field-affine-finite-dim` is the existing Mathlib leaf used in step 3.

3. WANTED:

None.

4. What was checked or corrected:

The item statement agrees with Stacks Tag 06LH, algebraic case: a finite-type scheme over a field with dimension at most zero is affine and finite, and the preceding paragraph's finite-over-a-field conclusion gives finite-dimensional global sections. I searched the DAG and blueprint for the Tag 06LH conclusion and found the existing node `lem-pc-algebraic-dim-zero-affine-finite`; I found the existing finite-over-a-field leaf for the global-sections clause. I searched the slopmaster2 source for the item tag and the relevant finite/dimension declarations and found no sorry-free declaration stating this item exactly.

Step 1 uses the statement of `lem-weil-pbc-closed-immersion-proper`, which explicitly says a closed immersion is proper and of finite type, and the definition node `def-weil-finite-type-morphism` for finite-type morphisms; the remaining composition observation is the direct affine-cover calculation from that definition. Step 2 uses exactly the existing node's statement, with its finite-type and dimension hypotheses matched to `Z`. Step 3 uses exactly the existing leaf's statement, applied to `Z -> Spec(k)`, to obtain the canonical affine presentation and finite-dimensional global sections. All hypotheses were checked against the item statement. Small cases checked: `Z` empty, `Z = Spec(k)`, and `Z = Spec(k[ε]/(ε^2))`; all satisfy the stated conclusions. The item blueprint reference already identified `lem-pc-degree-base-change` and the finite annihilator-subsheme sentence; its `same_as` search remains empty.

5. What remains unfinished:

Nothing.

## Review by E1

I read the item source at Tag 06LH and the source passages for the finite-over-a-field statement at Tag 03J3. I opened each cited node before writing `citations.json`: the closed-immersion node states finite type as part of properness, the algebraic zero-dimensional node states affineness and finiteness for a finite-type zero-dimensional scheme, and the finite-over-field leaf states the affine global-sections presentation and finite-dimensionality. The proof steps use those statements in that order and do not rely on the proof bodies of the cited nodes. I verified the field, finite-type, closed-immersion, and dimension hypotheses at the point where each is applied, and tested the empty, reduced point, and nilpotent point cases. No new node was needed, so there are no new Mathlib leaves or duplicate blueprint nodes.
