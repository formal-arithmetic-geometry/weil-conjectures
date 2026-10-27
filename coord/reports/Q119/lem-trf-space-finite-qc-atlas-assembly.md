# Q119 stage-1 report: lem-trf-space-finite-qc-atlas-assembly

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-space-finite-qc-atlas-assembly.json`: existing item split, statement and statement dependencies unchanged. Six proof steps, all below 2000 characters. No new nodes; no Mathlib leaves created.
- `citations.json`: one verbatim statement excerpt for each cited node in each step.
- `searches.jsonl`: actual logged Mathlib queries, with no invented searches; retained by the search command.
- `report.md`: this report.

## Attachments

None. Searched `lean/WeilConjectures` for the exact blueprint id and for algebraic-space and atlas terminology. No project declaration states the entire item. Open-atlas gluing and universal-thickening atlas declarations concern different objects. Existing `Sheaf` declarations are reference interfaces, not evidence of a finished upstream proof.

## WANTED

None. All sources used are in the read clone. No SGA source is used.

## Corrections and scope

No statement dispute or mathematical correction was needed. The item already permits empty J and nonaffine W_j and Z; those clauses are preserved. Tag 040T concerns finite unions of algebraic spaces, not the whole atlas assembly: the proof now builds the atlas through scheme tests rather than claiming 040T proves the assertion. The proof is marked agent-written because it supplies the omitted details in Topologies 0217 and assembles several source facts. The statement has not been weakened.

Read the chapter and unit records and the latest blueprint's `sk-i-curve-zero/lem-trf-local-term-locality.proof.md`. This is a historical polarized-descent helper in that node's existing ancestry. Its finite-atlas assembly serves step 4 of `lem-trf-space-qc-separated-etale-local`; it does not change the chapter or the contracting-correspondence unit route. The blueprint ancestor and via chain are retained and `same_as` remains empty after the whole-blueprint atlas/disjoint-union search. No repair note exists for this item. There was no earlier sandbox item or report to continue.

## Mathlib searches

The item retains all inherited Q110 searches. Five further queries ran through the required msearch.py under this item: LeanFinder for a finite local atlas assembly; Loogle for AlgebraicSpace and etale; grep for AlgebraicSpace and quasi-compact atlas wording; LeanSearch for the finite disjoint-union atlas; and LeanFinder for gluing maps to sheaves and composing covers. All services answered. Their actual top hits are recorded in the item and search log. Results concern scheme precoverings, scheme open-cover compactness and Zariski gluing, rather than an algebraic-space atlas. In particular QuasiCompactCover.of_finite is a predicate about covering families and does not assert this algebraic-space conclusion. The second phrasing found LocalRepresentability and Cover.glueMorphisms, again scheme/Zariski constructions rather than this assertion.

## Not duplicates

No new node is created. Reused the existing general scheme coproduct, open-immersion base-change, Zariski-to-fppf, sheaf-axiom, full Yoneda, scheme-source representability, etale-cover pullback/composition, finite-coproduct base-change and etale-locality nodes. In particular the existing algebraic-space-coproduct lemma constructs a coproduct of targets; it does not itself construct the map into the single target A here. The existing small-etale coproduct-representation lemma assumes different site and target data. Neither is substituted for the item.

## Review by Q119

I read Stacks `spaces-properties.tex` Tags 03E3 (definition-quasi-compact), 040T (lemma-finite-disjoint-quasi-compact) and 03EC (lemma-etale-over-space), `spaces.tex` Tag 025W (lemma-representable-diagonal), `schemes.tex` Tags 01JB (lemma-glue) and 01JC (lemma-glue-schemes), and `topologies.tex` Tags 0217 (lemma-etale), 021N (lemma-zariski-etale-smooth-syntomic-fppf). I checked the tag-label table rather than relying on changing section numbers. There are no new-node sources to audit.

Step 1 uses the precise open/disjoint/covering assertion of scheme-coproduct-family, open-immersion-base-change for the inverse-image subschemes, Zariski-coverings-are-fppf to use A's fppf sheaf axiom, algebraic-space for that sheaf hypothesis and sites-and-cohomology for its equalizer definition. Those statements are open in the read clone and give exactly these facts. The section formula, compatibility on empty intersections and restriction uniqueness are written explicitly, so this is an application of definitions rather than an unexposed gluing lemma. It constructs q without assuming Yoneda preserves coproducts.

Step 2 uses space-representable-etale-scheme-tests for every scheme-source map being representable, not a definition misquoted as a theorem. Its statement has no extra hypothesis on the map to A. Algebraic-space gives the precise etale/surjective scheme tests. Full Yoneda, not just full faithfulness, converts the test map to h_Z into T to Z.

Step 3 uses etale-covering-base-change on T to Z and the stated jointly surjective etale family W_j to Z. The test B_j to A times_Z W_j is defined by the two compatible projections. The actual hypothesis on q_j gives the scheme E_j and its surjective etale projection, exactly by the algebraic-space scheme-test definition. Etale-covering-composition then supplies both etaleness and joint surjectivity of E_j to T; no flatness or point-lifting theorem is inferred just from a definition.

Step 4 uses finite-coproduct-base-change only with a scheme target U, coprojections U_j to U and a scheme test V to U; J is finite as its statement requires. It is not applied over an algebraic-space base. The D_j/E_j comparison is proved by compatible tuples, with the additional W_j coordinate uniquely forced and its Z equation checked. Both directions are natural. Full Yoneda turns that explicit natural bijection into an isomorphism, preserving the T projection. This is a short universal-property calculation, not a new theorem hidden behind the word identification.

Step 5 uses the open summands of scheme-coproduct-family and the iff in etale-local-on-source to show the test projection etale. Its surjectivity follows directly by following the jointly surjective e_j into the coproduct. Algebraic-space is cited only for the meaning of representable surjective etale.

Step 6 uses the definition of scheme quasi-compactness and the covering coprojections. A finite union of finite selected sets is finite, so the compactness argument is a few lines and does not merit a new node. I tested J empty: Z must be empty; every T mapping to it is empty and all tests are vacuous, while U is the empty quasi-compact scheme. I also tested an empty summand, a singleton identity cover, nonaffine qc charts, an infinite J as a negative control (compactness can fail), and a nonseparated base. No separation, affineness, finite-presentation bound, or quasi-compactness of W_j to Z is used.

For C4 I checked every quoted excerpt against the cited node's statement, and the tuple computations use no facts from a dependency's proof. For C1 the non-elementary covering permanence, representability, source locality and coproduct comparison are all cited. For B there are no invented nodes, hollow data or search claims; the item retains its standalone statement and blueprint fields. For D the item carries the construction and calculations, not restatements delegated to new nodes. For E the objects and all base-change arrows are named, and all hypotheses above match. No step exceeds 2000 characters. The generic full-Yoneda tool use is declared in split_report; the sheaf-axiom definition is also documented there. No dependency reaches back to the item in the intended proof route; the server checks will verify acyclicity.

## Unfinished work

None in the one-level stage-1 split. Existing dependencies retain their own stage status. The required server dry run exited successfully: `OK (not pushed) deliver/Q119/lem-trf-space-finite-qc-atlas-assembly at b160c450082: preflight passed`. The dependency closure contains 147 existing nodes and does not reach this item. The statement and stmt_deps remain identical to the live item.
