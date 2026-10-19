Files written:

- `lem-trf-local-graded-flat-module-finite-presentation.json` — statement, split into four Tag 053C proof steps; no new nodes; Mathlib searches recorded.
- `citations.json` — verbatim statement quotes for every cited node in every step.

Attachments: none.

WANTED: none.

The original node was unsplit and had the Tag 053C statement but no proof. I retained its hypotheses and statement, filled the blueprint location and split report, and expanded the proof. The first step constructs the homogeneous presentation and uses the existing flat-kernel lemma. The second checks finite degree pieces, uses the existing retract-flat and finite-flat-local-free statements, and explicitly obtains finite generation of each kernel degree from the split surjection onto a free degree piece. The third reduces to the residue field, invokes the existing Noetherian finite-type and Noetherian-submodule statements, and chooses homogeneous residue generators. The fourth applies the existing Nakayama statement degreewise and concludes with the finite-presentation definition.

## Not duplicates

- `lem-trf-local-graded-flat-module-finite-presentation` vs `lem-trf-valuation-finite-type-module-presentation`: the latter is the valuation-ring finite-type theorem whose proof invokes this local graded theorem; it has a different base hypothesis and conclusion context.
- `lem-trf-local-graded-flat-module-finite-presentation` vs `lem-trf-valuation-flat-finite-module-presentation`: the latter concerns essentially finite-type algebras over valuation rings and is strictly more specialized, with no grading in its statement.
- `lem-trf-local-graded-flat-module-finite-presentation` vs `lem-sc-p1-finite-graded-module-lower-bound`: the latter is a graded-module degree-bound result, not finite presentation of a flat module.

## Review by Q82

I read the item node, the unit `dag/units/sk-i-curve-zero.json`, the chapter `dag/chapters/sec-trace-formula.json`, the Tag 053C statement and proof in `literature/stacks-project/more-algebra.tex` (lines 5856–5909), and the current blueprint ancestry recorded on the item. I also searched the source repositories for the exact blueprint tag and declaration; no finished Lean declaration states this item.

For Step 1 I checked that the finite homogeneous generating family gives the graded free presentation, that positive weights make each polynomial degree piece finite free, and that the cited `lem-weil-pbc-flat-ses-kernel-flat` statement exactly says the kernel is flat when the middle and quotient are flat. For Step 2 I read the statements of `lem-weil-pbc-flat-module-retract`, `lem-weil-pbc-finite-flat-local-free`, `def-weil-pbc-mv-polynomial-ring`, and the flatness definition. I corrected the imported proof's compressed claim that a kernel degree is finite: the surjection onto the free module `L_d` splits, so `K_d` is a retract of a finite free module and therefore finite; local finite-flat freeness then makes it free.

For Step 3 I verified that the residue-field polynomial ring is finite type over a Noetherian field, so the cited `lem-weil-pbc-finite-type-algebra-noetherian` applies. The tensorized kernel injects into the finite free tensorized source because `L` is flat, and `lem-weil-pbc-noetherian-submodule-finite` gives finite generation; homogeneous generators can then be selected degreewise. For Step 4 I checked that each degree map has finite source and target, so its cokernel is finite, and the quoted Nakayama statement applies over the local ring to lift residue generators. The final exact sequence is precisely the cited definition of finite presentation.

I tested edge cases conceptually: `n=0`, the zero module, a field as the local ring, and degree pieces with no monomials (which are zero and hence finite free). No source error or statement dispute was found. No new node was required, and every non-elementary input is an existing DAG node or a cited definition.

What I could not finish: none.
