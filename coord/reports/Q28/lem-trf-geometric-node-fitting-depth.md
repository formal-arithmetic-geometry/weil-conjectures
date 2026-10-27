# Stage-1 worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-geometric-node-fitting-depth.json`: statement, split; no exact Mathlib match. The statement and its eight statement dependencies are unchanged. Added five proof steps and their exact dependency union, source provenance, blueprint accounting, tool-use declarations and the actual searches from this run.
- `citations.json`: fourteen entries, one for every step/node pair, quoting the exact statement text used.
- `report.md`: this report. The search command generated `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. All ingredients already have DAG nodes, including the two statement-only ingredients `lem-trf-rational-nodal-completion-algebra` and `lem-trf-binary-quadratic-model-depth`; their proofs remain separate stage-1 tasks. I did not split or modify them.

## Attachments

None. Searching the live project under `lean/WeilConjectures/` for the exact blueprint tag, nodal/geometric-node terms and Fitting terms found no declaration stating the item. The uses of “nodal” in the pro-etale lisse-cover commentary are unrelated. The many project Kähler-differential lemmas do not assert this nodal first-Fitting/depth criterion.

## Literature wanted

None.

## Problems found and changes

No statement dispute. In particular, the hypothesis only supplies an abstract ring isomorphism of completions; replacing it silently by a K-algebra isomorphism would be unjustified. I explicitly cited the existing rational-nodal coefficient-rectification node before applying the relative differential comparison. No global dimension-one hypothesis on Spec R was added: the argument uses the completed model directly, rather than applying the scheme-level 0C4D equivalence outside its dimension hypothesis.

The existing blueprint provenance passes through the historical nodal-family/specialization branch below `lem-trf-local-term-locality`. The current main-20261015 blueprint ancestor is the contracting-local-term lemma and contains no separate nodal local-algebra assertion. I retained the provenance and recorded that limitation explicitly, rather than claiming a nonexistent sentence of the current ancestor. `blueprint_refs.py ancestor` confirms that ancestor, and whole-blueprint search for `nodal` found zero blueprint nodes. The chapter and unit were read and remain untouched; this is not the unit's key statement.

The Mathlib searches were run through msearch.py: LeanFinder with two distinct natural-language phrasings, Loogle with `KaehlerDifferential, IsLocalRing`, grep with `nodal|Fitting|fittingIdeal` in RingTheory, and LeanSearch. I read every returned hit/type. The hits concern smoothness, DVRs, cotangent ranks, height and Lie/module Fitting decomposition; none states the ordinary-node Fitting/depth assertion. The source node's inherited searches were retained, and this run's verbatim logged query/results were appended. There were no unavailable services in this run.

## Unfinished work

None for this one-level split. No Lean was written or compiled. The existing unsplit supporting nodes are cited as statements, as the one-level contract requires, rather than treated as completed formal proofs.

## Review by Q28

I read the full delivery-errors B–E checklist, the stage-1 brief, SETUP's three blueprint levels, GOAL, the chapter and unit records, the current ancestor blueprint, and the source text of Stacks curves.tex Tags 0C49 (lemma-nodal-algebraic), 0C4C (lemma-fitting-ideal), and 0C4D (lemma-nodal). I also read varieties.tex 0C52 (lemma-complete-local-ring-structure-as-algebra), algebra.tex 00MC (lemma-completion-faithfully-flat), 05CK (lemma-faithfully-flat-universally-injective), 0337 (lemma-apply-grothendieck), and more-algebra.tex 07NW (lemma-completion-depth). No SGA source is used. There are no new nodes requiring a separate source audit.

For step 1 I read the statements of `lem-trf-separable-closed-point-formal-presentation` and `lem-trf-rational-nodal-completion-algebra`. The first explicitly supplies both rings being Noetherian local, the extended maximal ideal being the completed maximal ideal, and residue field K. Its finite separable residue hypothesis holds because the residue extension is the identity K/K. The second has exactly our finite-type, rational-point and abstract-ring-isomorphism hypotheses and explicitly supplies the continuous K-algebra presentation with kernel (uv). Its conclusion does not require a dimension-one hypothesis. Thus the relative coefficient structure used later is obtained from a cited statement, not inferred from the abstract isomorphism. The images x,y generate the maximal ideal because the displayed local-algebra quotient has maximal ideal (u,v)/(uv).

For step 2 I read the differential definition, the differential-localization node and the Fitting independence/base-change node. The definition's symbol relations give the finite-generation argument written in the step: finitely many algebra generators give finitely many differentials. Localization says exactly that the localized differential module is Ω of B over K. The arbitrary-ring-map clause of the Fitting statement, rather than its special localization-away clause, applies first to R→B and then B→B̂. This justifies both displayed equalities. No tensor-exactness fact is silently needed here: arbitrary base change is already in the cited Fitting statement.

For step 3 I read the full statement of `lem-trf-completed-jacobian-differentials`. It allows any continuous coefficient-compatible formal presentation with finitely generated kernel. Here the field section is the given K structure map, the kernel is the single element uv, and n=2. Its output really is a module isomorphism, not only a statement about cotangent dimensions. The presentation column is (y,x), since the two partial derivatives of uv are v,u. I then used the actual row-kernel definition in the Fitting node: all rows are scalar multiples of that relation column, and the scalar-one row is present, so their one-by-one minors generate precisely (x,y). This explicitly checks the convention and rules out a hidden indexing shift.

For step 4 I read the completion-flatness and ideal-contraction statements. Noetherian locality was established in step 1, so completion is faithfully flat. Contraction applies to each of the two original ideals separately. It yields J_B=n from equality after extension, without an assumption that the completion map is surjective or an identification of ordinary with continuous differentials.

For step 5 I read the entire binary-quadratic depth statement, the depth and regular-sequence definitions, the completion-flatness statement and the flat-local depth formula. The quadratic uv has nonzero coefficient b=1, satisfying the model-depth hypothesis in every characteristic. Invariance under an isomorphism is checked directly on multiplication injectivity and successive quotients. The depth formula requires both rings Noetherian and the map flat and local: step 1 and the completion-flatness node supply these, and the extended maximal-ideal description verifies locality. The closed fibre is K, whose depth is explicitly zero by the regular-sequence definition; it is not assigned infinite depth, since K is nonzero and its maximal ideal is zero. This proves precisely the two required equalities of depths.

I checked the unchanged statement's definition citations: finite-type algebra, localization, completion, Kähler differentials, index-one Fitting ideals, algebraic closure, multivariate power series and depth all have the intended statements. The cross-unit general depth formula and the depth definition are declared as generic tool uses in split_report; the other cross-unit citations are Mathlib leaves. No unit step is replaced.

For small cases I checked R=K[u,v]/(uv) at (u,v), where the presentation directly gives Fitting ideal (u,v), and depth one. In characteristic 2 the Jacobian is still (v,u), so the computation loses no factor of 2. A field or a smooth rational curve does not meet the nodal-completion hypothesis (embedding dimensions 0 and 1); the double line has only one independent partial derivative, or zero in characteristic 2, and the cusp has Jacobian ideal (u²,v) in characteristic different from 2,3, so neither is accidentally treated as a node. In characteristic 2 or 3 the cusp ideal becomes still smaller. Additional components or larger-dimensional pieces of Spec R away from q do not enter this local argument.

Finally I checked the cited nodes' actual statement and proof dependencies for a path back to the item: none exists. The proof-dependency list is exactly the union of the five uses lists. Every citation quote is a literal substring of its node's statement. No new statement-only node contains a proof because there are no new nodes, no item clause has been relabelled as a lemma, and the calculation is carried in the item's own steps. The steps have lengths 673, 619, 775, 360 and 993 characters: none exceeds the 2000-character long-step threshold. No field of another node, no unit/chapter record, and no file of the read-only repository or launcher was modified.
