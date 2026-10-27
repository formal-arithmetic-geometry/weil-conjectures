## Files written

- `dag/nodes/sec-trace-formula/lem-trf-continuous-cover-nerve-comparison.json`: statement, now split into six proof steps; not a Mathlib leaf. The statement, three statement dependencies, source and existing blueprint provenance are retained. The proof uses two existing definition nodes. No new nodes and no new Mathlib leaves.
- `citations.json`: eight step/dependency entries containing verbatim statement excerpts.
- `report.md`: this report. `searches.jsonl` is the search command's existing log and has been retained.

## Attachments

None. Searches for `(blueprint: lem-trf-continuous-cover-nerve-comparison)`, the item id and covering-nerve/pullback-comparison terminology under `lean/WeilConjectures/` found no project declaration that gives the entire result. I read `CategoryTheory/SiteCechComplex.lean` and `Mathlib/AlgebraicTopology/CechNerve.lean`: the former constructs chosen tuple products and compares two choices in the same category, while the latter supplies diagonals into a single-arrow nerve. Neither proves preservation by the functor in this item's hypotheses. The sites continuous-functor extension concerns sheaf pushforward, not this comparison. The earlier searches of the upstream read source also found no exact attachment. No compiler or Lake command was run and no Lean was written.

## WANTED

None. The mathematical inputs used here are present in the local Stacks source and existing DAG statements.

## Corrections and scope

The live item had no proof; its statement is sound and is unchanged. There is no released repair note. The local sandbox contained only dispatcher markers and the genuine search log, and no delivery had been started when the launcher paused the session. The resumed work retained and reused those searches.

Stacks Tag 0D6X (`sites-cohomology.tex`, `lemma-pullback-injective-pre-limp`, lines 9277–9313 in the read copy) writes an equality of iterated fibre products in the proof of injective evaluation acyclicity. Tag 00WV (`sites.tex`, `definition-continuous`, lines 2522–2537) supplies exactly the fixed-cover base-change hypothesis used by that equality. The split expands this particular identity to the canonical isomorphism and its index-map compatibility. It does not assert that the functor is globally continuous or use the other cohomological assertions of 0D6X as black boxes. Since the finite-tuple induction and all-index-map equation are written out here, `proof_origin.by` is `agent`.

I read the chapter and unit records, the three levels in SETUP.md and the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/` ancestor statement and proof. The item is a generic cohomological-descent input below the existing `lem-trf-local-term-locality` provenance chain, rather than the unit's key node. I have not changed the chapter, unit, target, or their routes; no unit realization file is part of this delivery. Its proof-dependency edges point only to definitions, so no off-unit statement tool use is needed. There is no SGA citation.

## Search and duplicate check

The required `msearch.py Q119 lem-trf-continuous-cover-nerve-comparison ...` calls were actually run and their exact tools, queries and logged results were appended to the item. They comprise LeanFinder in two phrasings, Loogle, LeanSearch and a source grep. All five calls succeeded; there is no invented absence result from a failed service. Earlier imported search records are retained as history and were not relabelled as my own searches.

I read the relevant hits: `CategoryTheory.Functor.PreservesPairwisePullbacks.preservesLimit` in `Sites/Precoverage.lean:289–302` assumes pairwise preservation; `pullbackComparison` and its two projection equations in `Limits/Shapes/Pullback/HasPullback.lean:415–430` concern one binary pullback; `PreservesPullback.iso` in `Limits/Preserves/Shapes/Pullbacks.lean:131–145` requires preservation of that pullback. `PreservesLimitsOfShape.ofWidePullbacks` and `overPost` in `Limits/Preserves/Shapes/Over.lean:33–41` assume wide-pullback preservation, which is what the tuple induction must establish. None is the full item or a one-line specialization with these hypotheses. The other semantic hits concern morphism-property base change, cocontinuity, cover preservation, or stronger global finite-limit preservation.

The whole-DAG and blueprint searches for the item, `nerve`, `covering nerve`, `iterated fibre`, `fibre products`, the source tag 0D6X, and categorical pullback-preservation terminology were read. The generic finite-limit result `lem-weil-pbc-finite-limits-from-terminal-pullbacks` assumes a final object and preservation of all pullbacks; it cannot be applied here. The existing `def-weil-pbc-site-cech-complex` already states the tuple universal property needed for every step. Thus I create no parallel preservation node, no elementary rebracketing node and no node restating an item clause. The searches found no blueprint node equivalent to the item; `blueprint.same_as` stays empty.

## Not duplicates

No new nodes were created, so there are no new-node/existing-node tag pairs to distinguish. In particular, the arbitrary-index tuple universal property is reused from `def-weil-pbc-site-cech-complex`, rather than copied into a new node.

## Review by Q119

I checked the source of the item directly in the Stacks text: 0D6X uses continuity to identify a fixed covering's tuple products; 00WV(2) says preservation of base changes of a covering member along every arrow to its target. Our induction uses exactly the original member $f_j:U_j\to U$ along $W_{\mathbf s}\to U$. It does not require the prefix map to be a covering member, and does not apply the hypothesis to a different covering or an arbitrary pair of source arrows. The hypothesis that the image family is a covering supplies the necessary target pullbacks. I corrected the draft to cite site axiom (iii) explicitly in steps 2 and 3; this avoids taking existence of those pullbacks from a node that only defines chosen tuple products.

For step 1 I opened `def-weil-pbc-site-cech-complex` and checked its statement, clause (a): compatible arrows lift uniquely to a tuple product, and a singleton product is the object itself with identity projection. This justifies existence of the canonical comparison from the functorial images of the projections and starts induction at positive length one. No terminal object enters.

For step 2 the same node's clauses (a),(b) give the prefix map and the tuple uniqueness used to verify both inverses of $W_{(\mathbf s,j)}\leftrightarrows W_{\mathbf s}\times_U U_j$. I checked the two maps' types, their composites to $U$, and the identities after every projection. `def-weil-pbc-sites-and-cohomology` clause (1)(iii), also opened and read in full, explicitly states existence of fibre products of a covering member with an arbitrary arrow to the covered object; that is precisely why $R$ exists. The binary universal property is written in the step itself. This is elementary rebracketing, not an additional claimed lemma.

For step 3 I checked that the image family is a covering of the target site, so the same site axiom applies to $u(a)$ and $u(f_j)$ and supplies $Q$. The isomorphism $b$ is the item's assumption with $V=W_{\mathbf s}$, not a consequence being smuggled in from another node. The equations for its two projections are what “canonical map” means. The displayed inverse of $b u(h)$ has the correct order and its composites reduce by functoriality and the two identities of step 2. Lifting to $Q$ and applying this inverse gives the indicated unique pair-lift to $u(W_{\mathbf t})$. The cited tuple definition and the explicitly stated binary universal property suffice; no general finite-limit-preservation theorem is used.

Step 4 states the inductive universal-property claim for an arbitrary test object of the target category, not just a test object in the image of $u$. Its prefix lift exists and is unique by the induction hypothesis. The common-base equation uses an actual first prefix index, so I verified that the prefix is nonempty. The last-coordinate pair then satisfies step 3's hypothesis. I checked both existence and uniqueness of the longer tuple lift; equality of prefixes follows from their component equalities by the induction hypothesis. This is the substantive finite induction, marked non-elementary to distinguish it from the individual projection computations; it does not invoke a further unproved fact. Its cited node's clause (a) says exactly the universal-property claim being verified.

For step 5 I checked the statement, not the proof, of the cited tuple definition: clause (a) explicitly gives unique projection-compatible isomorphism of two tuple products. Step 4 has established that the mapped source cone is such a product, so this applies. The step also states the inverse construction and checks both composites by projections. Thus the particular canonical map of the item, rather than an unspecified isomorphism, is invertible for arbitrary independent tuple choices.

For step 6 I checked clause (b)'s exact equation for each index map and clause (a)'s uniqueness. Each term in the displayed equality has target $u(U_{t_{\alpha(k)}})$. After functoriality, both composites are $u(p_{\alpha(k)})$. This proves the requested equality for every function of indices, including repetitions, permutations and degeneracies; no injectivity or ordering assumption on the index function is used. The citation quotations in `citations.json` are literal parts of these opened node statements and cover every proof `uses` entry.

I tested the statement at an empty covering (no positive-length tuples, so the result is vacuous), a singleton covering (length-one comparison is the identity, longer repeated tuples are handled by the same hypothesis), length two (the first binary comparison), repeated indices and index permutations. In a category of sets the inverse-lift recipe sends a compatible tuple to its unique compatible tuple, so no choice-dependent identification is being assumed. The proof never considers the empty tuple, never presumes a final object, and never uses preservation of arbitrary pullbacks. Since the source gives no nontrivial lemma behind the displayed identity, there is no omitted standard lemma to create. All six steps are below 2000 characters; the only non-elementary step is the explicit induction step, with the base and induction claim already written. There are no new statement-only nodes whose source, meaning or small cases would need a separate audit.

Against delivery-errors B–E, I checked full statements and notion dependencies, exact source tags and labels, single TeX escapes, actual search records, absence of a duplicate or circular citation, and every hypothesis in each use. The source's equality is treated as the canonical isomorphism already stated in the item; no statement dispute or silent weakening is needed. The completed server validation is recorded below; the final delivery command repeats preflight before pushing.

## Validation

Server `srvcheck.py ... review_split` exited 0 with PASS (zero new nodes). The required `deliver.py Q119 lem-trf-continuous-cover-nerve-comparison --no-push` exited 0 with `OK (not pushed)` at `a3b1c8ab690`: server preflight passed, including the prescribed DAG and split checks. Exact-quote coverage and the unchanged statement/dependency union were also checked by reading JSON; there are eight quotation entries and six proof steps, each below 2000 characters. No local project checker, compiler, Lake command or repository write was run. The final report update is validated again before the push.

## Unfinished work

No mathematical part of this item remains unfinished. The independent maintainer review remains part of the delivery process.
