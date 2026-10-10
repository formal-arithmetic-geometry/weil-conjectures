Files written:

- `dag/nodes/sec-picard-framework/lem-pc-pseudo-coherent-bounded-finite-free-model.json`: statement node split into three proof steps; Mathlib searches found no match.
- `citations.json`: no external node citations; the construction is written directly in the item steps.

Attachments: none.

The source was read in `/home/ubuntu/c1-stacks-review/more-algebra.tex`, More on Algebra, Lemma 15.66.5 / Tag 0658, for the finite-free replacement and truncation construction.

The Lean source was searched under `WeilConjectures/` for the item id, the Tag 0658 terminology, and pseudo-coherent finite-free model declarations. No sorry-free project declaration states this item exactly. The imported node already had the correct statement and blueprint ancestor, so its statement and dependencies were retained. No auxiliary node is part of this split; the finite-free replacement argument is written directly in Step 1.

## Review by F1

I read the target node, its `lem-sc-finite-duality` blueprint ancestor, and the `sk-thm-picard-duality` unit. I checked the item against More on Algebra, Lemma 15.66.5 / Tag 0658 in `/home/ubuntu/c1-stacks-review/more-algebra.tex`.

Step 1 matches the source's explicit direct-summand construction: the kernel is a sum of contractible two-term complexes. Step 2 is the direct cohomology invariance of a quasi-isomorphism. Step 3 matches the source's descending split-surjection cancellation above `b`, including replacement of finite projective complements by the Step 1 finite-free model; finitely many upper degrees give termination. I tested the construction on the zero complex, a module concentrated in degree `b`, and `b=0`; each gives the claimed zero-above-`b` finite-free model. No statement or dependency outside this item was edited.

## Not duplicates

The item shares Tag 0658 with broader or differently formulated nodes, but none states this bounded-above finite-free model conclusion as its own statement: `lem-pc-pseudo-coherent-bounded-finite-free-model` vs `lem-weil-bounded-finite-tor-perfect`: the latter concludes perfectness from finite Tor dimension and does not state the upper-bound truncation model; `lem-pc-pseudo-coherent-bounded-finite-free-model` vs `lem-pc-ring-pseudo-coherent-finite-tor-perfect`: the latter assumes finite Tor dimension and concludes a bounded projective model, while this item only assumes cohomology vanishing above `b` and gives a bounded-above free model; `lem-pc-pseudo-coherent-bounded-finite-free-model` vs `lem-trf-finite-tor-amplitude-perfect`: the latter is a derived-category perfectness criterion, not the explicit finite-free truncation assertion.

## Second reading by F1

- Item statement: checked hypothesis by hypothesis against More on Algebra Lemma 15.66.5 / Tag 0658; verdict agrees, including the zero-above-`b` finite-free conclusion.
- Step 1: checked against the source's displayed direct-summand construction and contractible-kernel argument; verdict repaired to state that construction explicitly.
- Step 2: checked against quasi-isomorphism invariance of cohomology and the source's vanishing hypothesis; verdict elementary and correct.
- Step 3: checked against the source's descending induction, split surjection in the top degree, and contractible summand removal; verdict repaired to state the split and finite-free replacement explicitly.
- New nodes: none; the imported item is the only edited node, so B1-B7 and duplicate-node checks are vacuous.
- Small cases checked: zero complex, a module concentrated in degree `b`, and `b=0`; all satisfy the statement.
- Changes: corrected the stale `created.item` ownership metadata; replaced vague replacement/truncation prose with the source construction; corrected the report's source and auxiliary-node claims.
