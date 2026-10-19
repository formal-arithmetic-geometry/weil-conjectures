Files written:

- `dag/nodes/sec-trace-formula/lem-trf-separable-residue-coefficient-section.json` — statement, split proof, and no new nodes; the separable-algebraic square-zero input is an existing Mathlib leaf (`Algebra.FormallyEtale.of_isSeparable` as recorded by `lem-exc-separable-algebraic-square-zero-lifting`).
- `citations.json` — three verbatim statement quotes for the two proof steps.

Attachments:

- No exact sorry-free project declaration was found for this item in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`.

WANTED:

- None. The cited Stacks source is present locally.

What was checked and corrected:

- The imported item is exactly More Algebra Tag 0C34, with the complete local $k$-algebra and separable residue-field hypotheses unchanged. The source proof reduces the claim to formal smoothness of the separable residue field and then uses the continuous lifting lemma.
- No new auxiliary node was created. I searched the DAG and blueprint for Tag 0C34 and for coefficient-field lifting statements; the only relevant existing results are the Mathlib leaf `lem-exc-separable-algebraic-square-zero-lifting` and the generic adic complete-target lifting node `lem-weil-pbc-fs-adic-lift-into-complete`.
- No source error or statement dispute was found. The blueprint ancestry remains the imported `lem-trf-local-term-locality` route and the split report records the coefficient-field-section paragraph it realizes.

## Review by Q90

I read the item statement and More Algebra Tag 0C34 at `literature/stacks-project/more-algebra.tex` lines 9590–9608. I also read the complete statements of every cited node: the square-zero lifting leaf, the adic formal-smoothness definition, and the complete-target lifting theorem. In step 1, the separable-algebraic leaf supplies a lift for every square-zero quotient; taking the source ideal to be zero makes the condition exactly the adic formal-smoothness definition, since every positive power of zero is zero. In step 2, I checked each hypothesis of the complete-target theorem with $A=R$ and $I=J=\mathfrak m$: completeness is the item hypothesis, $J^1\subseteq I$ is equality, the closedness equality is tautological because $I=J$, and the residue map kills the zero source ideal and has image in the zero quotient ideal. Its conclusion is precisely a $k$-algebra section whose residue composite is the identity. The three entries in `citations.json` are verbatim substrings of the cited statements. I tested the statement on $R=k$ (section the identity), on $k[[t]]$ (constant-coefficient inclusion), and on a complete local ring with an inseparable residue field, where the hypothesis correctly fails. `srvcheck.py ... check_dag` returned `check_dag OK`.

Nothing remains unfinished.
