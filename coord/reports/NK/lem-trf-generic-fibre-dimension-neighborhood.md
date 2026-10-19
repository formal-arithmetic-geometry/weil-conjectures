# Stage-1 worker report

Files written:

- `lem-trf-generic-fibre-dimension-neighborhood` (statement; Mathlib verdict: no match): split the imported Tag 05F7 item into three proof steps; no new statement nodes were needed.
- `citations.json`: verbatim statement excerpts for every node used by every proof step.

Attachments: none. No declaration in `WeilConjectures/` carries this item or the blueprint tag, so this is not an attachment.

WANTED: none.

What was wrong: the imported item had the correct Tag 05F7 statement but no completed proof split. I retained the statement and its source, and expanded the Stacks argument. The historical `created` metadata is retained unchanged.

What could not be finished: nothing. No Lean source or compiler was edited or run; this delivery is stage 1 only.

## Review by NK

I read the item node and the source proof in `literature/stacks-project/more-morphisms.tex`, More on Morphisms, Tag 05F7, lines 8411--8432. The source first removes the closed locus where local fibre dimension exceeds `n`, then spreads a closed subset meeting the generic fibre, and finally intersects the two opens. I checked the statements of every cited DAG node in the repository, including their source and hypotheses: `lem-weil-pbc-local-fibre-dimension-open` (Tag 02FZ) supplies openness of the locus where the local fibre dimension is at most an integer; `lem-sbc-generic-fibre-closed-avoidance` (Tag 054W) applies to locally finite type quasi-compact morphisms and gives an open whose fibres over the closure of the chosen point avoid a closed set; `lem-sbc-generic-closed-subset-fibre-nonempty` (Tag 055G) applies to finite type morphisms and spreads a closed subset meeting the generic fibre; `def-weil-finite-type-morphism`, `def-pc-scheme-fibre`, `def-sc-generic-point`, `def-kun-topological-krull-dimension`, and `def-kun-topological-dimension-at-point` state the definitions used in the argument.

Step 1 defines the closed locus `Z` where local fibre dimension is greater than `n`. I verified that the cited openness node states exactly the needed complement, that finite type supplies the locally finite type and quasi-compact hypotheses required by Tag 054W, and that the generic-point definition justifies `closure {eta} = Y` in the irreducible base. The generic fibre hypothesis makes `Z` disjoint from the generic fibre, so the avoidance node gives the open upper bound.

Step 2 treats the edge case `n = 0` separately: the Krull-dimension definition says the empty scheme has dimension below every nonnegative integer, so the generic fibre is nonempty and Tag 055G applies with `C = X`. For `n > 0`, I checked that the local-dimension definition together with finite generic-fibre dimension gives a point of local dimension `n`; the second closed locus is therefore nonempty on the generic fibre, and Tag 055G gives the lower-bound open. This avoids introducing the undefined expression `n - 1` in the zero case.

Step 3 intersects the two opens. I checked that the generic point belongs to both, hence the intersection is nonempty, and that the upper and lower local-dimension bounds imply fibre dimension exactly `n`. The final comparison uses only the cited Krull-dimension and local-dimension definitions. I also checked empty-fibre and zero-dimensional edge cases, verified that no hypothesis was added or dropped, and recorded that no SGA source was used.
