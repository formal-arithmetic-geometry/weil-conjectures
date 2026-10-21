# Q92: lem-a1-integral-stratum-chart-restrictions

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-integral-stratum-chart-restrictions.json`: statement; split into nine steps using existing DAG statements. Statement, statement dependencies, source, created metadata and blueprint ancestry retained. Added actual Mathlib search records. No new nodes and no new Mathlib leaves.
- `citations.json`: 21 step/node pairs with verbatim statement quotations.
- `searches.jsonl`: six searches executed through the required msearch command. Both semantic phrasings were read; Loogle returned presheaf pullback constructions; the source search located the elementary coefficient and site infrastructure. None states this entire item. Read `Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean` and the general presheaf pullback comparison: these define coefficients or ordinary pullback, not the stratified completed-integral result.

## Attachments

None. Searched the whole `lean/WeilConjectures/` tree for the blueprint tag and integral/stratum/chart/Roos notions, and inspected the more focused stratified-perfect matches. No project declaration states every clause of this item with a finished proof. The item has no recorded Lean declaration to attach.

## WANTED

None. The source for this item is available locally. No new node requires additional literature.

## What was wrong or incomplete

The imported item had no proof. Its statement is retained. In particular I retained the distinction between exact restriction along immersions and site objects and the arbitrary completed pullback along h or a chart projection. I did not use the parent item's global t-exactness assertion. The conclusion about the bound of the scalar model is a cohomological bound; it does not bound the degrees of the chosen projective representative.

The existing DAG already contains the general stratified-perfect characterization, immersion comparison, slice comparison, integral composition and completed-triangle results needed here. Creating individual nodes for those clauses would duplicate existing work. I declared the generic results from other units as tool uses, with a reason for each. These serve the first paragraph of `lem-a1-finite-map-purity`, through the two ancestors recorded in blueprint.from; they do not replace the unit's finite-fibre/Frobenius route. The chapter and unit records are untouched. The current main-20261015 proof of `lem-a1-finite-map-purity` and the unit and chapter records were read.

## Unfinished work

None in this one-level split. Existing cited unsplit statements remain their owners' stage-1 work. This delivery introduces no new pending lemmas.

## Not duplicates

No new nodes. Reused existing statements even where they are more general than the item: particularly `lem-weil-pbc-integral-stratified-perfect-characterization`, `lem-sf-immersion-completed-pullback-comparison`, `lem-sp-slice-restriction-strict-derived-limit` and `lem-pod-integral-pullback-composition`. Blueprint searches for constructible pullback, locally closed, perfect values, immersion limit and integral pullback found no blueprint statement equivalent to this complete conjunction.

## Review by Q92

I read Bhatt--Scholze, Proposition 6.6.11 and its perfect-values convention on p.54, together with its proof; Lemma 6.5.8 on p.50, Lemma 6.5.9 on pp.50-51 and Remark 6.5.10. Proposition 6.6.11 uses topological Noetherianity, whereas the item assumes the stronger scheme Noetherianity. I read the local Stacks text for 09AA (`proetale.tex`, lemma-closed-immersion), 099M (lemma-naive-completion), 099N (lemma-pushforward-Noetherian-case), 022D (`topologies.tex`, lemma-fpqc) and weakly etale base change in `more-morphisms.tex`. The extra projection and shift specifications are an explicit agent assembly of the existing DAG statements; I marked proof_origin as agent, rather than attributing these specifications verbatim to the paper. There are no new node sources to review.

For Step 1 I read the entire statement of `lem-weil-pbc-integral-stratified-perfect-characterization`. Its final clause expressly identifies the category in the question, including the same coefficient ring and reduction functors; its equivalence (ii) supplies the precise perfect scalar charts. X has every hypothesis: Noetherian, finite-dimensional and ell invertible. A bounded finite-projective representative supplies the ordinary displayed scalar complex: the constant terms are flat because they retract finite free constant modules, and the statement of `lem-pc-bounded-above-flat-kflat-site` supplies K-flatness. I added that citation explicitly on the final C1 pass, so the termwise calculation does not hide this criterion. This avoids assuming without a theorem that the uniform-reduction definition and the paper's category coincide.

For Step 2 I checked `lem-weil-pbc-proetale-immersion-limit-preservation` for exactness and all small limits, and `lem-sf-immersion-completed-pullback-comparison` for the actual coefficient identification, finite reductions, completeness and comparison with completion. I read `lem-a1-integral-pullback-completed-comparison`: it compares the specified integral functor with completed pullback on all derived-complete inputs, identifies the actual projections and is linear and shift compatible. The inverse of the ordinary-to-completed comparison composed with gamma has the correct direction to identify integral pullback with ordinary restriction.

For Step 3 I read all clauses of `lem-sfb-proetale-object-inverse-image-restriction`, including its assertion for rings and abelian sheaves. Thus module actions restrict as well, not only constant-ring modules. `lem-pur-site-restriction-module-adjunction-exact` applies to an arbitrary ring sheaf, gives exactness and an actual left adjoint, and hence the restriction is a right adjoint preserving limits. `lem-sfb-adic-stratum-completion-unit` explicitly covers the finite reductions and completion unit on the stratum and its covering slice. Its Noetherian input is X (later W), not the chart V. `lem-sp-slice-restriction-strict-derived-limit` states the natural isomorphism and each projection compatibility, not just existence of a derived limit. Gamma then identifies the specified integral construction. No unproved assertion that an arbitrary inverse image preserves countable products is used.

Step 4 uses exactly the coordinate comparison stated by `lem-pur-roos-additive-comparison`. Its hypotheses have been established for each restriction: additivity and invertible countable-product comparison. I wrote the equation identifying the restricted transition endomorphism before applying it, and explained passage to derived categories using exactness established earlier. This checks the actual strict-tower maps rather than an unspecified cone isomorphism.

Step 5 uses the statement of `lem-weil-pbc-local-derived-restriction-comparisons`, which explicitly gives the cohomology comparison for actual inverse-image coefficients followed by a slice. I checked that Steps 2-3 supply the required coefficient identifications. The vanishing assertion is then an immediate application of an exact functor to zero. It does not require a globally t-exact completed arbitrary pullback.

For Step 6 I checked the statement of `lemma-constructible-pullback-stratification`: it constructs the fibre-product strata with their actual inverse-image subsets. I checked the assumptions of `lem-sc-affine-noetherian-underlying-space` on each affine of W and of `lem-sfb-noetherian-space-compact-subsets` on those resulting spaces. This supplies constructibility of the locally closed strata. For the covers, the existing Mathlib leaf `lem-weil-pbc-weakly-etale-composition-base-change` supplies base change of weakly etale maps; `lem-galois-fpqc-covering-base-change` supplies the covering-family assertion. Both parts are needed for a pro-etale covering. All fibre products are the ones over the stated base; no factorization is inferred from set containment.

For Step 7 the first clause of `lem-pur-integral-operations-preserve-constructible` is exactly the needed constructibility and canonical-reduction assertion, with no finiteness or linearity assumption on h. Its statement also applies to the stratum and chart arrows. All source and target schemes have ell invertible by their structure maps. This places the unprimed restricted complex in the domain required for integral composition. The primed restriction argument uses W Noetherian, which is an input; it does not require the charts to be Noetherian.

For Step 8 I read `lem-pod-integral-pullback-composition` including the orientation of c, its arbitrary-scheme hypotheses, naturality and its finite-reduction normalization. The composite written in the step first uses the inverse of c for q',h, then c for g,q, then the chart composition comparison. The equality h q' = q g is the fibre-product equality. This gives the asserted map with the requested finite-level reductions; no assertion about finite-level evaluations alone determining a derived morphism is used.

For Step 9 `lem-cbc-completed-pullback-triangles` is explicitly about the specified strict completed construction, coherent shifts and distinguished triangles, without scheme Noetherianity assumptions. Gamma supplies both the coefficient-datum comparison and shift compatibility for the exact functor in the question. I wrote how to transport the last arrow of a triangle and justified linearity on both cone coordinates. Step 7 supplies closure in the integral constructible subcategories.

I tested zero K, the empty source or target, empty pulled-back strata, the identity map, and a one-stratum constant perfect model. The statements impose no nonemptiness conditions; discarded strata and empty charts cause no assertion about a nonzero stalk. A torsion model R/pi in degree zero confirms that the cohomological bound is distinct from a finite-projective representative's term bound. All nine steps have fewer than 2000 characters. Every dependency was opened and checked, every citation has a verbatim quote in citations.json, and a read-only dependency traversal found no path from any proof dependency back to this item. The B-E checklist required no new nodes: all non-elementary operations have existing cited statements, no proof of a cited node is used as its interface, and no conclusion was moved into a new restatement node.

## Validation

The first required server dry run passed at ec4ca4437c3. The final C1 pass added the existing bounded-above-flat K-flat criterion to Step 1 and its verbatim citation; the final dry run checks that version before push.
