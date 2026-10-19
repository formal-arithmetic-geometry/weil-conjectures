Files written:

- `dag/nodes/sec-trace-formula/lem-trf-proper-birational-curve-finite.json` — statement, split proof, and blueprint metadata; no Mathlib match for the curve theorem.
- `dag/nodes/sec-trace-formula/lem-trf-birational-curve-quasifinite.json` — statement-only supporting node; no Mathlib match.
- `citations.json` — verbatim statement quotes for every cited step.

Attachments: none.

WANTED: none.

The imported item had an empty proof. I kept its statement and hypotheses unchanged. The source's Tag 0AB7 argument is most transparently realized by first isolating Tag 0AB6's codimension-one quasi-finiteness statement as a strictly smaller node, then applying the existing proper locally quasi-finite implies finite Mathlib leaf (`pqf-lem-proper-lqf-finite`). The existing `cor-pqf-proper-quasifinite-finite` node was not cited because the Mathlib leaf gives the same implication with a directly usable closed declaration. No source error or statement dispute was found.

## Not duplicates

`lem-trf-birational-curve-quasifinite` vs `pqf-lem-proper-lqf-finite`: the new node proves quasi-finiteness for dominant finite-type maps of integral curves with finite generic extension; the existing leaf assumes proper locally quasi-finiteness and concludes finiteness for arbitrary schemes.

`lem-trf-birational-curve-quasifinite` vs `pqf-lem-qf-finitefibres`: the existing node characterizes quasi-finiteness by finite type and finite fibres; it has no integral-curve or function-field hypotheses and does not supply the codimension-one argument.

`lem-trf-proper-birational-curve-finite` vs `lem-trf-proper-birational-normal-curve-iso`: the existing theorem adds normality of the target and concludes isomorphism, while this item has no normality assumption and concludes only finiteness.

## Review by Q19

I read the item in `dag/nodes/sec-trace-formula/lem-trf-proper-birational-curve-finite.json`, the neighboring normal-curve node that cites it, and the unit `sk-i-curve-zero`. I checked the source `literature/stacks-project/varieties.tex`: Tag 0AB7 states that a proper morphism over a one-dimensional Noetherian local target is finite near the target point when the generic residue-field extension is finite; its proof invokes Tag 0AB6, whose condition (1) gives quasi-finiteness over each such point. I also read the exact Tag 0AB6 statement and proof, and verified the tag labels in `literature/stacks-project/tags/tags`.

Step 1 uses `lem-weil-pbc-finite-type-over-noetherian`, whose statement says that a finite-type scheme over a Noetherian scheme is Noetherian, to justify that the finite-type curve C has Noetherian local rings. It then checks the dimension-one local bound directly from the definition of the scheme dimension, checks local finite type of the k-morphism p on affine charts, and observes that the function-field isomorphism is a finite generic extension. These are exactly hypotheses of Tag 0AB6 condition (1), so the cited new node states precisely the resulting quasi-finiteness conclusion. Step 2 uses the existing Mathlib leaf `pqf-lem-proper-lqf-finite`, whose statement is the proper and locally quasi-finite implies finite theorem; Step 1 supplies local quasi-finiteness and the item supplies properness, so all hypotheses match and the finite conclusion is exactly the item.

For the new node I searched the whole DAG and both blueprint snapshots for the Tag 0AB6 statement and for proper birational curve quasi-finiteness; no existing node stated it. I ran the required LeanFinder, LeanSearch, Loogle, and Mathlib grep searches and recorded their actual no-match results. I also checked the existing proper-plus-quasi-finite leaves and the neighboring normal-curve theorem for the duplicate comparisons above. Small cases checked were the identity map of A¹ (quasi-finite and finite), the open immersion A¹ minus the origin into A¹ (quasi-finite but not proper, showing why Step 2 needs properness), and the normalization of a cusp (finite birational but not an isomorphism without target normality). The server-side `check_dag` and `review_split` checks both passed before this report was written.

What was corrected: the item now has a complete two-step proof, exact proof dependencies, filled blueprint place and `same_as`, and the new supporting node has its own blueprint ancestry and searches. No hypotheses or conclusion were changed.

What could not be finished: nothing.
