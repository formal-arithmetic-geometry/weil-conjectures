# Stage-1 report: lem-sfb-split-completion-local-invariant-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-split-completion-local-invariant-descent.json: item, statement unchanged, status split, five complete proof steps.
- citations.json: seven citations, each quoting verbatim the statement of the node used by that step.
- report.md: this report.
- searches.jsonl: actual search log maintained by the prescribed msearch command.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves used: lem-weil-pbc-power-series-domain, lem-weil-pbc-faithfully-flat-ideal-contraction, lem-weil-pbc-local-completion-faithfully-flat; the two definition nodes used in step 1 are also existing Mathlib leaves.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, split completions, reduced nodal rings and nodal reducedness found no declaration proving all clauses. The returned smooth-lifting, normalization and curve-assertion references concern other statements and do not supply an attachment. No Lean was written and nothing was compiled.

## WANTED

None. All source material needed is present locally.

## Findings and corrections

The live statement is correct. It no longer asserts a differential Fitting-ideal or depth comparison. Its inherited Mathlib searches mostly concern that older assertion; I preserved them and appended searches for the actual current statement. The Loogle query containing Ideal.Quotient was rejected by the service as an unknown identifier; this is explicitly recorded as an invalid query, followed by the corrected MvPowerSeries kernel query. The returned kernel declarations concern maps on coefficient rings, not restriction of two variables to the axes. The local pinned Mathlib does not contain the remotely indexed MvPowerSeries/Ideal.lean, so those results are not treated as local matches. The local domain instance was found at MvPowerSeries/NoZeroDivisors.lean:141 and is already represented by lem-weil-pbc-power-series-domain.

The source 0C49 supplies the reducedness argument, and 0C4D the geometric-stalk descent. I give the split-model argument explicitly by coefficients, rather than making a new node for a clause of the item. The canonical map A to B and its Noetherianity are already stated with exactly this arbitrary-extension evaluation data by lem-trf-separable-evaluation-local-base-change, so no duplicate auxiliary node is needed. A local search of transitive dependencies confirms that this existing lemma and the other cited results do not depend on the item.

I read the current latest blueprint's sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md (3), as well as the recorded unit/chapter. The inherited blueprint ancestry has null from.node; blueprint_refs.py ancestor returns None for it. I preserve that existing ancestry and make its proof place and realization explicit. The local algebra implements the recorded nodal-reduction branch below the unit and makes no alteration of the unit route. The off-unit evaluation-local-base-change lemma is declared as a generic tool in split_report.tool_uses.

## Unfinished work

None in this stage-1 split. Its dependencies remain subject to their own existing stages. There is no new unsplit node.

## Not duplicates

No new nodes are proposed. Whole-DAG concept searches and blueprint_refs.py searches for completion, nodal, and reducedness were read; the existing generic evaluation lemma and the three Mathlib theorem leaves are reused.

## Review by NC

I read Stacks curves.tex at Tag 0C49 (lemma-nodal-algebraic), especially the proof of (3) implies (1), and at Tag 0C4D (lemma-nodal), the arbitrary-field paragraph descending reducedness. I also read varieties.tex Tag 0C4Y (lemma-change-fields-flat), its affine-localization proof, and Tag 0C50 (lemma-change-fields-algebraic-unramified), together with algebra.tex Tags 00MC (lemma-completion-faithfully-flat) and 05CK (lemma-faithfully-flat-universally-injective). No new node requires a separate source audit.

For step 1 I opened the statements of def-weil-pbc-multivariate-power-series and def-weil-pbc-algebra-hom-quotient. The former states coefficientwise addition and the convolution product, which justify both axis restrictions as ring homomorphisms. A coefficient of a product on an axis only involves coefficients on that axis. Vanishing on both axes is precisely vanishing of the coefficients a_i0 and a_0j; shifting the remaining array by (1,1) explicitly produces g with h=uvg. The quotient definition gives the quotient relation and kernel, so equality of two classes with the same image is checked by their difference. These are computations from definitions, not an uncited theorem on formal substitution or an implicit convergence argument.

For step 2 I read lem-weil-pbc-power-series-domain. Its statement applies to any domain and any finite number d of variables, so taking A=L and d=1 proves that each factor is a domain for every field L, including characteristic 2. A positive power vanishes in a domain only for zero, by induction. Thus neither reducedness of a product nor descent along an injection is used as an unproved black box: both are the displayed componentwise argument and step 1's injectivity. This step is marked non-elementary because it uses the cited power-series domain theorem.

For step 3 I read the whole statement of lem-trf-separable-evaluation-local-base-change, not merely its proof. It introduces exactly the finite-type S, maximal p, finite separable residue F, arbitrary extension K, embedding iota, evaluation epsilon, and localized A and B of this item. It explicitly concludes that A and B are Noetherian local rings and A to B is faithfully flat. All hypotheses are present; there is no hidden algebraic-closedness or dimension assumption. I then read lem-weil-pbc-faithfully-flat-ideal-contraction, whose final sentence explicitly says that a faithfully flat ring map is injective. That is exactly what this step uses.

For step 4 I read lem-weil-pbc-local-completion-faithfully-flat. It requires a Noetherian local ring, now supplied by step 3, and it completes at that ring's maximal ideal. Here this ideal is n=qB, so its inverse limit and canonical map are exactly the specified B-hat and B to B-hat. It supplies faithful flatness, and the same explicitly injective clause of ideal contraction supplies the second injection. There is no appeal to injectivity of an arbitrary localization or to completion of a non-Noetherian ring.

For step 5 each map sends a zero positive power to a zero positive power. Applying the ring isomorphism, step 2, and its injectivity proves reducedness of B-hat; applying the two canonical injections proves reducedness of B and A successively. This proves every clause without needing a K-linear isomorphism. It is elementary and cites no additional node. I checked the small cases K=k, S=k, and a zero-dimensional nonreduced S=k[e]/(e^2): the injections still hold, while the split-completion premise appropriately fails in these zero-dimensional examples. The model argument over F_2 has the same kernel (uv); u and v are nonzero zero divisors, which is consistent with reducedness and does not accidentally assert that the quotient is a domain.

Against delivery-errors B--E: all data and definitions stay explicit, no new clause is relabelled as a lemma, no new statement hides a proof, every non-elementary input is a cited existing statement, and each citation has a verbatim statement quote in citations.json. There is no cycle through the chosen tools. All five steps are shorter than 2000 characters, and none hides a comparison lemma. I preserved the item's statement, source, creation record and ancestry, and only supplied its proof and stage-1 metadata with the new logged search evidence.
