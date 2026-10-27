# Stage-1 report: lem-sc-finite-etale-diagram-local-normal-form

## 1. Files written

- dag/nodes/sec-curve-estimates/lem-sc-finite-etale-diagram-local-normal-form.json: statement, split; retained its statement and original search records, added five proof steps and the searches actually run by Q34.
- citations.json: all thirteen step/node citations, with verbatim statements as quotes.
- No new nodes, hence no new Mathlib leaves. Existing local splitting, coproduct base change and clopen decomposition statements suffice.

## 2. Attachments

None for the item. Searches for its exact blueprint tag and the notions in lean/WeilConjectures found no declaration giving the complete finite-diagram assertion. AlgebraicGeometry.Scheme.FiniteEtale.exists_etale_isPullback_sigma (FundamentalGroup/LocallyTrivial.lean:40) proves only the one-object local trivialization. AlgebraicGeometry.finite_etale_etale_local_split (FiniteEtaleEtaleLocalSplit.lean:181) already belongs to lem-weil-pbc-finite-etale-etale-local-split; that closed node is used without editing it.

## 3. WANTED

None. Read literature/stacks-project/pione.tex, Tag 0BN9, lemma-finite-etale-covers-limits-colimits, especially the finite-colimits proof's splitting and further open refinement. Also read etale.tex, Tag 04HN, lemma-finite-etale-etale-local, and groupoids.tex, Tag 03YW, example-constant-group (functor of points of the disjoint union). The argument generalizes the two-arrow refinement of 0BN9 explicitly, so proof_origin is agent.

## 4. Discrepancies and dependencies

The item's statement is correct, including varying sheet counts and an empty diagram; no STATEMENT-DISPUTED correction is necessary. The existing lem-fet-locally-trivial statement still asserts one global finite sheet set, which fails on a disconnected base with different degrees. Its blueprint_update and current latest blueprint correct this to pointwise local triviality, as does the actual Lean theorem. This report does not edit that other node. The proof instead cites the existing closed pointwise 04HN node, lem-weil-pbc-finite-etale-etale-local-split. This is a generic tool from sk-thm-p1, declared in split_report.tool_uses; it supplies the exact same local splitting ingredient rather than changing the route.

Read the recorded chapter and unit, plus current literature/blueprint/latest/blueprint/sec-curve-estimates/_section.md and sk-thm-br/_section.md. The current blueprint moves lem-fet-finite-limits and lem-fet-locally-trivial under sk-thm-br and revises the former to finite limits, coproducts, group quotients and monomorphisms. The live auxiliary item is independently stated from Stacks 0BN9, and its object-trivialization / further-open-refinement content remains valid. No chapter, unit, target or ancestor node is changed.

## 5. Unfinished work

None for this one-level split. No Lean was written or compiled. No repository file was written and no git command was run in the repository. All proof dependencies existed before this delivery.

## Not duplicates

No new nodes. DAG and whole-blueprint searches for finite etale, finite diagram, simultaneous and coproduct copies found the existing one-object local splitting and the clopen morphism description used here; neither states this full finite-diagram assertion. In particular no elementary refinement fact or clause of the item was made into a new node.

## Review by Q34

I read B through E of delivery-errors.md (both repeated copies) and checked the actual statements of every cited node. I read the source of 0BN9 with its parallel pair normalization, 04HN's pointwise local splitting and 03YW's description of maps into base copies. The proof follows that normalization; it writes the finite induction and the refinement argument rather than citing the desired assertion under another name. The Mathlib searches were executed through msearch.py: LeanFinder with two distinct phrasings, Loogle, grep and LeanSearch. The hits give etale sites, stability, gluing and topological covering lemmas, not simultaneous algebraic finite-diagram normalization. I read the grep locations in ColimitsOver.lean and Properties.lean; they concern gluing cocones and nontrivial sections. The exact queries and actual results remain in searches.jsonl and mathlib_searches.

Step 1 uses def-galois-finite-limits-colimits for finiteness of both objects and arrows, and def-weil-pbc-finite-etale-category for the base change functor landing again in finite etale objects. These statements really include those facts. It initializes induction with the identity cover and handles empty Y separately.

Step 2 uses lem-weil-pbc-finite-etale-etale-local-split with the already finite etale next object over each current W, at every point w. Its statement supplies the point above w and all pieces isomorphic over the new base, not merely a decomposition of a geometric fibre. The coproduct universal property turns these isomorphisms into a trivialization. Etale composition is exactly clause (2) of lem-weil-pbc-etale-composition-cancellation. The finite-coproduct base change node preserves labels and projections, while def-pc-fibre-product's universal property identifies iterated products. Coverage is checked at every w, so no surjectivity of each individual neighborhood, common residue-field extension, quasi-compactness or global constant degree is assumed.

Step 3 uses clause (a) of lem-galois-coproduct-copies-morphisms-clopen: applied to each source summand, it provides both the clopen pieces and the exact formula for the restricted map. This is stronger than merely saying a map is locally constant. Finitely many arrows and finite source sheet sets give finitely many conditions. A Galois-category connected-component lemma would require connected bases and is deliberately not used.

Step 4 is an elementary finite intersection of the clopen pieces from step 3. It uses the same clause (a), finite-coproduct base change, and the open-immersion and composition clauses (1),(2) of the etale permanence node. The coproduct statement gives disjointness of target summands. The surviving point w makes each final open nonempty, so equality of the conjugate scheme maps forces equality of their sheet functions even without any connectedness hypothesis. I wrote the identity and composition equations and checked them on w, rather than claiming an unspecified compatibility. All functions with empty domain are unique; a nonempty source and empty target cannot occur on these nonempty opens. This also checks zero-degree covers. The step is elementary from the cited statements and the functor axioms, and is shorter than 2000 characters.

Step 5 assembles the set-indexed covers and the data already obtained; no further geometric theorem is used. Each induction level is a set-indexed union of point sets. For empty I, the same construction has no object or arrow data, with the empty finite intersection equal to W. For empty Y the family is empty. For disconnected Y with varying degrees, the finite sets are chosen separately on each member, as the statement requires.

I checked C1 by identifying every geometric input above as a cited existing statement, and C4 by copying its actual statement into citations.json (thirteen entries). The elementary work is finite induction, universal-property identification, finite intersection, pointwise function equality and set-index bookkeeping. No step exceeds 2000 characters. There is no new statement needing separate edge-case tests, no new node restating a clause, and no new proof dependency on the ancestor lem-fet-finite-limits, so the split introduces no circularity. The report retains the discrepancy in the unrelated stale trivialization statement rather than silently relying on it.


## Repair of returned delivery 101b4e50129

The return of 2026-10-24 10:08 UTC says the independent reader approved the split, but landing failed because the commit command could not find `coord/reports/Q34/lem-sc-finite-etale-diagram-local-normal-form.md` as a known git path. This is a report-path landing failure, not a compiler failure. I kept the existing sandbox proof, report, citations and search log and ran the required initial dry run before editing; it passed on the current server DAG at 3b4b35993e1.

I compared the retained returned node with the current live item field by field. The only differences were the intended stage-1 fields: proof, proof_deps, proof_origin, status, split_report and mathlib_searches. The statement, statement dependencies, source, chapter, unit, creation metadata and blueprint ancestry agree. I rebuilt the sandbox node from the current live metadata with the retained stage-1 work overlaid, leaving all other live fields intact.

I re-read all nine current statement/proof dependency nodes. For all eight proof dependency nodes, every saved verbatim quote from the returned delivery equals the current statement exactly: def-galois-finite-limits-colimits, def-weil-pbc-finite-etale-category, lem-weil-pbc-finite-etale-etale-local-split, lem-weil-pbc-etale-composition-cancellation, lem-sc-etale-fibre-product-base-change-coproduct, def-pc-fibre-product, lem-galois-coproduct-copies-morphisms-clopen and lem-weil-pbc-scheme-coproduct-family. I also re-read the statement-only dependency def-weil-etale-morphism. The local splitting node remains closed; the clopen node still provides the exact restricted-map formula used in steps 3 and 4. No changed hypothesis or clause requires replacing a citation.

The revised split makes explicit the construction suppressed by the sentence “This is a trivialization of the next object” in step 2. The isomorphisms of each piece with the new base induce inverse coproduct maps; their composites are identities by their restrictions to each summand. These maps are over the base because the piece isomorphisms are their structural maps. Step 2 now cites the existing scheme-coproduct node for precisely this universal property. I regenerated all thirteen verbatim citation entries from the current DAG and rechecked the proof-dependency union. This is a concrete proof and report revision, not an unchanged re-push. It creates no new node and changes no mathematical statement or proof route. All steps remain shorter than 2000 characters, and the previously checked empty and varying-degree cases still apply.

The updated report.md is supplied in the required sandbox location for deliver.py to package as the report path named in the return. I did not edit the landing scripts or create files in coord/; the standard delivery tool handles the current-base commit and report packaging.
