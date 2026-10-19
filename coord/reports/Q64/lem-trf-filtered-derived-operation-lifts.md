# Stage-1 delivery report: lem-trf-filtered-derived-operation-lifts

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-filtered-derived-operation-lifts.json`: retained the imported statement and its seven-step proof, marked `status` as `split`; no new nodes and no Mathlib leaves.
- `citations.json`: 25 verbatim statement quotations, one for every cited node at every proof step.
- `searches.jsonl`: the required Q64 LeanFinder, Loogle, source-grep, and LeanSearch queries and their outputs.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact item id, the blueprint tag, `FilteredDerivedOperation`, filtered-derived-operation terminology, and compact-support exchange terminology. The checkout has no declaration stating this item; the nearby exchange declarations are different statements. The reference master checkout likewise has no declaration of the item. No declaration with a sorry-free proof was used as an attachment.

## WANTED

None. The proof sources named by the item are available locally: Stacks `derived.tex` and `more-etale.tex`, and Varshavsky's trace-formula PDF. The pro-etale specialization is the explicit construction described in the imported proof.

## What was wrong or changed

The repository item was still `unsplit` even though it already contained a complete imported seven-step natural-language proof and a prior review note. I retained its statement, hypotheses, source places, dependency lists, blueprint ancestry, and proof text, and changed only its stage-1 status to `split`. I did not create a child node because every non-elementary input used by the proof is already an existing DAG node. The item's Mathlib searches were retained and rerun with the required `msearch.py` commands; Mathlib has only ordinary derived-category and adjunction declarations, not this filtered operation-lift theorem. No statement, route, coefficient category, compactification hypothesis, or arbitrary-transformation claim was changed.

## Not duplicates

No new node was created, so there are no new-node duplicate pairs. I searched the whole DAG and blueprint for filtered-derived-operation, filtered-injective, associated-graded, compact-support exchange, and adjunction-mate formulations. Existing filtered localization, injective-model, graded-comparison, pro-etale operation, compactification-tower, and mate-pasting nodes are cited as distinct inputs; none states the combined item.

## Review by Q64

I read the item node, `sec-trace-formula.json`, the `sk-i-global-additivity` unit record, and the proof/source places named in all seven steps. I also opened the statement of every node cited by every step; `citations.json` copies those statements verbatim. The item introduces the bounded-below finite-filtered derived categories, the forgetful and graded functors, the left-exact derived lift, exact termwise lift, filtered adjunction, the supplied compactification composite, and the canonical exchange/pasting clause. I checked that no cited statement is being used for its proof rather than for its stated conclusion.

Step 1 uses `def-sp-filtration`, `def-sp-filtered-complex-subquotients`, and `lem-weil-pbc-localization-universal-property` exactly for the filtration, graded quotient, and localization descent. Exactness identifies cycles, boundaries, cohomology, shifts, cones, and graded quasi-isomorphisms; the step does not assume a stronger abelian filtered category.

Step 2 uses the filtered localization/injective-model statement and the bounded-below injective-representative statement. I checked the finite descending split of each filtered injective term, the induced filtration under a left-exact functor, the natural graded quotient map, and the K-injective hypotheses before identifying both forgetful and graded outputs with ordinary derived functors. The edge cases of a zero filtration and a one-piece filtration agree with the construction.

Step 3 uses the filtered localization model and the graded-comparison statement. The exact left adjoint gives preservation of injectives; degreewise adjunction preserves each filtration inclusion and chain homotopy, so the Hom-set bijections give the filtered adjunction and triangle identities. The unit and counit are checked after forgetting and on every grade, and the invertibility conclusion is restricted to comparisons already constructed and to domains where their ordinary maps are isomorphisms.

Step 4 checks the coefficient hypotheses against the cited Grothendieck, injective-embedding, pro-etale operation, finite-ring exactness, extension-by-zero, and compact-support-candidate statements. The constant ring is finite commutative, inverse image is the ordinary uncompleted functor, `j_!` is the cited exact open operation, and the compactification is supplied rather than asserted to exist. The special field and `A_{E,n}` candidate is invoked only under that candidate node's own hypotheses; the displayed composite itself is valid for every finite commutative ring.

Step 5 checks each generating comparison against the cited pullback-composition, direct-image-composition, open-extension base-change, composite-adjunction, conjugate-uniqueness, and graded-comparison statements. The open composition map is the conjugate of the canonical inverse-image identification, and identity/pasting are degreewise identities. Thus the step constructs genuine filtered transformations and does not infer them from equality after forgetting.

Step 6 is the long recursive construction. I checked the explicit unit--square--counit mate, the proper/open refinement square, the clopen section projection, and the displayed filtered mate `gamma_Q`, including its source and target. The cone argument uses all graded inputs in the admissible domain and only then proves invertibility. The projection identities are componentwise elementary, while the geometric clopen assertion is taken from `lem-cbc-strict-tower-proper-open-calculus`; no tower-category theorem is silently used.

Step 7 is the long pasting calculation. I checked the proper mate-pasting statement, the supplied compatible compactification tower, the mixed proper/open cube identity, and the directions of all base-change and composition maps. The two expanded routes are the mate of the same pasted square; nested clopen projections and refinement comparisons cancel by the cited naturality and composition identities. The final equality is therefore for the actual compactification-derived exchanges on their admissible domains, with no appeal to faithfulness of forgetting and no fixed-field-linearity hypothesis. I checked the zero/identity-map and one-piece-filtration cases, which reduce to the corresponding ordinary identities.

All seven proof steps are non-elementary and cite their full dependency sets. The proof-dependency union equals the union of the step uses. The Mathlib searches record no matching filtered-operation-lift declaration; ordinary `CategoryTheory` derived-functor and adjunction hits are only general background and do not specialize in one line to this statement. No Lean was written, compiled, or run.

## What could not be finished

Nothing remains for this stage-1 split. The cited dependency nodes remain existing queue items or leaves for their own stage-1 work; this delivery does not split them or claim their proofs are finished.
