Files written:

- `dag/nodes/sec-trace-formula/lem-trf-finite-extension-module-finite-presentation.json`: item, statement, split proof, and blueprint metadata; no new nodes.
- `citations.json`: four verbatim node-statement quotes covering both proof steps.

Attachments:

- `lem-pc-module-finite-presentation-transitive` is the existing Mathlib leaf for `Module.FinitePresentation.trans`.
- `lem-weil-pbc-finite-algebra-presentation-module-presentation` is the existing Mathlib leaf for the finite algebra to finite module-presentation implication.

WANTED:

- None.

What was wrong or corrected:

The imported statement used the standard phrase “finite and finitely presented homomorphism” without spelling out the module and algebra meanings. I expanded it to “S is finitely generated as an R-module and finitely presented as an R-algebra,” citing the existing definitions. This is a definitional clarification of Algebra Tag 0564, not a change of mathematical content. The imported node had no proof; I supplied the two directions. I searched the DAG for Tag 0564 and the relevant finite-presentation phrases. The existing scalar-tower Mathlib leaf and finite-algebra leaf avoid introducing duplicate clause nodes.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## Review by NS

I read the item source and complete proof in `literature/stacks-project/algebra.tex`, Algebra Tag 0564, including the presentation argument and its reference to Tag 0561. I also read the statements of `lem-weil-pbc-finite-algebra-presentation-module-presentation`, `lem-pc-module-finite-presentation-transitive`, `def-weil-pbc-finite-type-algebra`, and `lem-trf-finitely-presented-over-subring` in the repository. Step 1 uses the first node exactly for the hypotheses that S is finite as an R-module and finitely presented as an R-algebra, then uses the second node exactly for the scalar-tower implication from S-module finite presentation to R-module finite presentation. Step 2 checks that finite R-module generators generate S as an R-algebra (every element is already an R-linear combination, hence a polynomial in those generators), then applies the finite-type definition and Tag 0561 node to transfer finite presentation from R to S. I verified all statement hypotheses and conclusions match the expanded Tag 0564 statement, checked the zero-module and identity-extension edge cases, and recorded verbatim quotes for every cited node in `citations.json`. The only correction was the definitional expansion of “finite and finitely presented”; no source error or missing dependency remains.

What I could not finish:

Nothing.
