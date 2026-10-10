Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-isogeny-surjective.json` — statement, split proof, no new nodes, Mathlib searches recorded.

Attachments:

- None. `AlgebraicGeometry.surjective_npow_points` is present in the slopmaster2 source, but its audit is `rests_on_sorry` and it is therefore not attachable as a closed declaration.

WANTED:

- None.

What was checked and changed:

- The item statement and its one proof step were checked against the blueprint node `literature/blueprint/master/blueprint/sec-abelian-varieties/sk-prop-av-divisible/lem-sc-isogeny-surjective.md`, the unit route in `dag/units/sk-prop-av-divisible.json`, and the Lean theorem at `WeilConjectures/AlgebraicGeometry/AbelianVariety/Isogeny.lean:387`. The statement keeps the blueprint's abelian variety over an algebraically closed field and positive integer hypotheses.
- Step 1 uses `lem-sc-isogeny-facts`; I opened that node and verified that its part (a) explicitly states that multiplication by $n$ is finite, flat, and surjective. It also uses `lem-sc-finite-flat-surj-points`; I verified that its statement explicitly concludes $f(X(k))=Y(k)$ for finite flat surjective morphisms over algebraically closed $k$. The displayed quotes in `citations.json` are verbatim portions of those statements. The combination is the complete one-step argument in the source: apply the first fact to `[n]`, then the second to obtain surjectivity on points.
- I searched the whole DAG and blueprint for duplicate statements and found no alternative node. Since the proof uses only the two existing nodes, no new node was created. The item has no independent Mathlib formulation: LeanFinder returned only generic divisibility lemmas, the requested Loogle pattern was rejected because `AbelianVariety` is unknown to Loogle, grep found no matching declaration, and LeanSearch was unavailable; these outcomes are recorded in `mathlib_searches`.
- The Lean audit was read in full. The theorem body is not `sorry` itself, but its transitive open declarations include unresolved sorry-backed results, so I left it unattached and documented that fact. No statement or hypothesis was weakened.

## Review by F1

I read the source blueprint paragraph, the unit step, both cited DAG node statements, and the Lean declaration. The item’s single step cites exactly the claims it consumes: finite, flat, surjective multiplication from `lem-sc-isogeny-facts`, followed by point-surjectivity from `lem-sc-finite-flat-surj-points`; no cited node is used for proof content beyond its statement, and the step is not marked elementary. I verified that the field is algebraically closed and that the morphism hypotheses match the cited point-surjectivity statement. I tested the edge case $n=1$ against the statements: multiplication by one is the identity and the conclusion is consistent. I also checked for duplicate DAG or blueprint nodes and found none. The only correction was completing the imported metadata (`same_as`, `status`, and `split_report`) and adding the required search and citation records; the mathematical route itself already matched the source.

What could not be finished:

- The existing Lean theorem cannot be attached because the recorded transitive sorry dependencies remain unresolved; this does not prevent the natural-language split from passing the stage-1 dry run.

## Second reading by F1

- Item statement: checked against the imported blueprint node `lem-sc-isogeny-surjective` and its Stacks source tag 03RP; the hypotheses (abelian variety over an algebraically closed field and `n >= 1`) and conclusion agree. The cases `n = 1` (identity map) and the zero-dimensional abelian variety (the trivial abelian variety) are consistent; `n = 0` is outside the stated hypothesis, and an empty scheme is not an abelian variety.
- Step 1: checked the statement of `lem-sc-isogeny-facts` (part (a) gives finite, flat, and surjective `[n]`) and `lem-sc-finite-flat-surj-points` (finite flat surjections of finite-type schemes over algebraically closed fields are surjective on points). The substitutions `X = Y = A` and `f = [n]` satisfy the latter hypotheses, so the step is complete and non-elementary.
- New nodes: none; the existing DAG nodes already state both required facts. I searched the DAG and blueprint for duplicate statements and found no alternative node to replace either citation.
- Mathlib/Lean audit: the recorded semantic searches found no exact Mathlib declaration; the Lean declaration `AlgebraicGeometry.surjective_npow_points` remains non-attachable because its transitive dependencies rest on unresolved sorry-backed declarations.
- Changed: removed the step's extra Tag 03RP parenthetical, which was not supplied by either cited node and was unnecessary to the argument; rewrote the step to make the morphism substitution and conclusion explicit. Added this second-reading audit; no node statements or hypotheses were weakened.
