1. Files written:

- `dag/nodes/sec-zeta-weil/lem-weil-shift-span-linear-recurrence.json`: statement split into four proof steps; no new DAG nodes.
- `citations.json`: verbatim citations for every node used by each step.

2. Attachments: none.

3. WANTED: Bourbaki, *Algèbre*, IV.5, Exercise 3 (the finite-dimensional shift-span/recurrence argument is quoted by Milne but not proved in the available literature). The proof is written directly from the standard linear-algebra argument.

4. No statement or source error was found. The source and blueprint state the dependence argument tersely; the split makes the zero-dimensional case, minimal dependent index, normalization, and coordinate reading explicit. The existing closed Lean declarations do not provide an exact attachment for this item with the order bound `d ≤ max(dim V,1)`.

## Review by Q45

I read the target node, the `sk-prop-criterion` unit and its chapter, the rationality-criterion blueprint proof, and Milne's cited pages. I searched the source checkout for the target tag and for shift-span/recurrence declarations; there is no declaration tagged for this item. The source's `PowerSeries.exists_forall_add_eq_zero_of_finiteDimensional_shiftSpan` gives a related recurrence but does not state the required minimal-order bound, so I did not attach it.

Step 1 was checked against the definitions of sequence subspace, finite-dimensionality, and dimension: every shift lies in the stated span, and dimension zero forces the span to be the zero subspace, giving the explicit `d = 1` case. Step 2 uses the existing statement `lem-weil-independent-family-card-le-dimension`, which says that an independent family in a finite-dimensional space has cardinality at most the dimension; applied to `R_0, ..., R_D`, it yields a dependent family and, by minimality, `d ≤ D`. I read that node's statement verbatim and recorded it in `citations.json`. Step 3 is the elementary definition of dependence followed by division by the nonzero last coefficient; minimality proves that coefficient is nonzero. Step 4 evaluates the sequence identity coordinatewise and uses the exact definition of eventual linear recurrence, with `m = 0`; its statement is also quoted in `citations.json`.

I tested the edge case `dim V = 0` explicitly and retained the bound `1 ≤ d ≤ max(dim V,1)`. The item has no new definition or dependency, and its proof dependencies are exactly the definitions and the one cited dimension lemma used by the steps.

## Second reading by Q45

- Statement: checked the target against the current `main-20261015` rationality-criterion section and proof, the imported master proof, and Milne, Ch. II §27, p. 157 (Bourbaki IV.5, Exercise 3); PASS. The hypotheses quantify over an arbitrary field and sequence, and the conclusion keeps the zero-dimensional case through `d ≤ max(dim V,1)`.
- Step 1: checked the sequence-space and span constructions against `def-weil-sequence-subspace` and `def-weil-submodule-span`, and the dimension-zero argument against `def-weil-finite-dimensional-subspace` and `def-weil-vector-space-dimension`; PASS. The cited span definition was added to the step and statement dependencies.
- Step 2: checked membership of every `R_j` in `V`, dependence of `R_0,\ldots,R_D`, and the minimal-index bound against the full statement of `lem-weil-independent-family-card-le-dimension`; PASS. Its Mathlib-backed declaration and the independent Lean Finder search were read.
- Step 3: checked the dependence relation, nonzero leading coefficient from minimality, and normalization by field division; PASS, elementary from the field and linear-dependence definitions.
- Step 4: checked coordinate evaluation and the `m=0` specialization against the full statement of `def-weil-eventual-linear-recurrence`; PASS, elementary after the cited definition.
- New nodes: NONE. I searched the DAG for span, shift, recurrence, and dimension statements; no new node is warranted. The existing dimension lemma is a Mathlib leaf, so no off-unit unsplit tool is declared.
- Edge cases: tested the zero sequence (`V=0`, `d=1`), a one-dimensional nonzero span (`d=1`), indices `n=0` and `n=1`, and an arbitrary field including a two-element field. The empty-scheme case is inapplicable because this is a field/sequence statement.
- Search audit: added the independent `leanfinder` query “linear independent family cardinality at most finite dimension field” to `searches.jsonl` and `mathlib_searches`; it found the existing finite-dimensional cardinality declarations but no exact shift-span theorem.
- Changes made: added `def-weil-submodule-span` to `stmt_deps`, step 1 `uses`, `proof_deps`, and `citations.json`; recorded the independent search. No mathematical statement, source citation, or proof step was weakened.
