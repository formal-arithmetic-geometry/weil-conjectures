## Files written

- `dag/nodes/sec-trace-formula/lem-trf-formal-binary-morse.json` — repaired item split with five proof steps; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-binary-morse-tangent-substitution.json` — repaired statement-only auxiliary node; no Mathlib match.
- `citations.json` — verbatim statement quotes for every cited node in every item step.

## Attachments

No sorry-free project declaration states the item. No attachments.

## WANTED

None. The proof source `literature/stacks-project/curves.tex` is present.

## Not duplicates

- lem-trf-binary-morse-tangent-substitution vs lem-trf-formal-binary-morse: the auxiliary node states convergence and invertibility for an arbitrary sequence of tangent substitutions, while the item additionally constructs corrections that send its particular series to its quadratic part.
- lem-trf-binary-morse-tangent-substitution vs lem-trf-formal-jacobian-quadratic-criterion: the auxiliary node states the generic substitution limit theorem; the existing Jacobian criterion only invokes formal normalization and does not state convergence or invertibility of tangent substitutions.
- lem-trf-binary-morse-tangent-substitution vs lem-trf-rational-node-quadratic-completion: the auxiliary node is a formal power-series automorphism theorem for arbitrary tangent corrections, while the existing rational-node statement concerns descent of a completed geometric node to a ground-field quadratic quotient and does not state substitution convergence or invertibility.
- The homogeneous correction observation was checked against the DAG and blueprint and is elementary from the invertible two-element basis; it is now a proof step rather than a new node.

## Source error

The returned proof's induction applied the changing substitution to `f`, so `f(x_r,y_r)-Q(x_r,y_r)` retained the order of `f-Q` and could not be forced into the next power; for example, `f=uv+u^3` has a cubic error under every tangent substitution. Its final line also identified `Q(x_infty,y_infty)` with `Q` instead of with the image of `Q` under the limiting substitution. I corrected the route by keeping `f` fixed in the identity `f=Q(x_r,y_r)+E_r`, using positive corrections whose polar contribution cancels the leading class of `E_r`, and defining the desired automorphism as the inverse of the limit substitution.

## What was wrong or incomplete

The homogeneous-correction node was removed because its statement is the two-line basis calculation already required as an elementary proof step (C1). The tangent-substitution node had an unused polynomial-ring dependency and malformed `\mathfrak p` notation; its statement now cites the formal-series definition inline, keeps only the field and power-series dependencies, and uses the corrected notation. Both new-node blueprint `from.via` lists now begin with `lem-trf-formal-binary-morse` followed by the item's inherited route. The item's proof dependencies and citations were updated after removing the node, and the final step now reads `f=\beta(Q)` followed by `\alpha=\beta^{-1}`.

## What could not be finished

No Lean code or compiler was used, as required for stage 1. The tangent-substitution node remains `unsplit` for later queue work.

## Review by Q50

I read the item source at `literature/stacks-project/curves.tex`, Tag 0C49, including the proof of `lemma-nodal-algebraic` from the successive change of generators through the complete-limit argument. I compared every item hypothesis with the imported statement: a field, the formal binary power-series ring and its maximal ideal, an order-two part `Q=au^2+buv+cv^2`, the nonzero discriminant, the tangent-to-identity condition, continuity, and no characteristic restriction. The item statement is unchanged. I also reread the existing formal-series definition node and the tangent-substitution node statement after repair.

Step 1 uses the formal-series definition for homogeneous expansion and the elementary determinant calculation showing that the two polar forms are a basis; it initializes the fixed identity `f=Q(x_2,y_2)+E_2` with `E_2` in `p^3`. Step 2 is the elementary finite-dimensional basis observation: a degree-one factor is expanded in the `L_1,L_2` basis and the remaining factor has degree `r`; I checked this on `Q=uv` in characteristic two and on a general invertible polar matrix. Step 3 keeps `f` fixed, checks that the corrections have order `r`, expands `Q` modulo `p^(r+2)`, and verifies that the degree-`r+1` class cancels; the two-correction terms have order `2r >= r+2`, and the tangent condition is preserved. Step 4 reindexes the increments exactly as the tangent-substitution statement requires (`r_n,s_n` in `p^(n+1)`), so that node supplies the limits and the continuous automorphism `beta`. Step 5 uses the errors in every successive power and completeness to obtain `f=beta(Q)`, then applies the inverse automorphism to get `alpha(f)=Q`; this fixes the returned direction error.

For the remaining new node I checked its hypotheses and conclusion word for word, including the field, the explicitly cited formal-series construction, the maximal ideal notation, the required powers, convergence, continuity, automorphism, and inverse substitution. I searched the whole DAG and blueprint by its key phrases and found no duplicate. Its Mathlib searches were reread from `searches.jsonl`: LeanFinder, Loogle, grep, and LeanSearch found only general power-series substitution or renaming results, with no theorem giving the required tangent automorphism. The item's existing Mathlib searches were likewise reread and still address the unchanged target statement. The citation file now quotes the exact statements of the formal-series and tangent-substitution nodes for every step that uses them. I checked the returned B3, B4, B9, C1, E3, and E4 points individually and corrected each one in the files above.
