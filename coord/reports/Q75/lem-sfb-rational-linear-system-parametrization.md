# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-rational-linear-system-parametrization.json`: unchanged statement, split into five explicit elementary induction steps; no new nodes and no Mathlib leaves.
- `citations.json`: empty list, because the proof steps invoke no external node statements.

## Attachments

None. Read-only searches of `lean/WeilConjectures/` for the exact blueprint tag, the item id, rational solutions, Gaussian elimination, and echelon terminology found no declaration stating the whole item. The constant-rank and residue-kernel matrix modules concern other statements, and their existence does not give an attachment.

## WANTED

None. This is an agent-written direct finite-coordinate proof. Milne, *Abelian Varieties*, II §1, Lemma 1.3, printed pp.77–78 (PDF pp.83–84) was read for the inherited source context. It discusses finite rational algebras and their real extension, but does not assert this parametrization. The node explicitly preserves that distinction and marks its proof as agent-origin.

## What was wrong or incomplete

The imported statement is correct but had no proof. I preserved it verbatim. An initial private draft separated rational particular solutions and kernel spanning into two new nodes; self-review against delivery-errors D1 found that these merely isolated the item's clauses. Those drafts were withdrawn from the delivery. The final proof carries the actual pivot argument and has no new nodes.

The chapter and recorded unit were read, along with the current latest blueprint unit at `sec-six-functors-basics/sk-thm-sf-ctf-stability/`. The legacy unit record differs from the latest unit text, but this auxiliary finite-coordinate lemma changes neither version's route. `blueprint_refs.py ancestor` returns `None`, matching the item's inherited null ancestor and full via chain. Whole-blueprint searches for “rational affine parametrization” and “linear system” found no equivalent statement (the latter returns only the ample-line-bundle definition). The use by the already reviewed parent, rational-positive-definite-feasibility step 2, requires exactly this affine-parametrization statement and remains valid.

## Mathlib searches

The inherited search records are preserved as historical records supplied with the item. New searches were run through the required `msearch.py` command and logged in this sandbox's `searches.jsonl`: LeanFinder for consistent rational affine parametrization, a second phrasing using Gaussian elimination over a subfield, Loogle `Matrix.mulVec, Rat.cast`, LeanSearch for rational particular solutions and nullspace directions, and grep for scalar-extension kernels, rational solutions, row reduction, and diagonal-transvection existence. The hits were read. The number-field basis-matrix equalities concern a particular embedding matrix; the simplex entries are metaprograms; the Presburger results concern natural-number semilinear sets. The general square-matrix transvection factorization in `Matrix/Transvection.lean` requires additional rectangular/inhomogeneous work and is not a one-line specialization to this statement. The tensor kernel identity in `TensorProduct/Tower.lean:899` cancels a repeated base change on an already extended source and is not the rational-kernel spanning assertion. Thus no exact Mathlib leaf or project attachment was found.

## Not duplicates

No new nodes are delivered. No equivalent imported blueprint statement was found.

## What could not be finished

Nothing remains for this item's stage-1 split. No Lean was written or compiled, no compiler or Lake command was run, and no repository or launcher file was changed.

## Review by Q75

I checked delivery-errors B through E against the final node. There are no new statement-only nodes to audit, no new Stacks tags, no Mathlib-leaf claims, and no off-unit tool citations. The existing `def-weil-field` statement was opened and supplies the field notion actually used in the unchanged item statement. The proof uses just finite sums, rational field arithmetic, the injective usual inclusion into the reals, permutations of finite coordinates, and induction on the number of columns. It does not invoke a Gaussian-elimination or kernel-extension theorem without a citation: the elimination itself is written out.

Step 1 sets up induction uniformly in the row count, handles zero columns and the zero matrix, and explicitly chooses coordinate directions when there are no constraints. Step 2 chooses an actually nonzero entry (possible only after excluding the zero matrix), tracks both the row and coordinate permutations, and solves the pivot equation using its nonzero rational coefficient. Step 3 writes each reduced coefficient and right side, expands each original equation, and checks the equivalence over both fields. The pivot remains nonzero in the reals; no irrational pivot is used. Thus the real consistency hypothesis passes to the smaller rational system. Step 4 uses the induction hypothesis only at strictly fewer columns and writes the particular and homogeneous lift formulas, checking each row. Step 5 substitutes the full real parameter expression, distributes the finite sums, and undoes the coordinate permutation, so it proves the assertion for every solution rather than only one.

I checked the boundary cases $d=0$, $m=0$, $A=0$, one row, one column, and $k=0$. For example, a one-column nonzero pivot leaves no free coordinates, while a zero system returns all coordinate vectors. Inconsistent zero rows are excluded by the stated real-solution hypothesis. No conclusion or hypothesis was changed. Each proof step is shorter than 2000 characters and contains only the displayed routine calculation or the explicitly declared induction step; there is no independent comparison lemma hidden inside. All proof uses lists are empty and their union is the empty proof-dependency list, so `citations.json` is correctly empty. The rejected two-node draft is not part of this delivery.
