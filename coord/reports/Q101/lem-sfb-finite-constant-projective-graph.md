# Stage-1 report: lem-sfb-finite-constant-projective-graph

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-constant-projective-graph.json`: statement, split; seven proof steps, all geometric inputs reused from the DAG. The statement is unchanged. Three definition dependencies already cited in its text were restored to `stmt_deps`.
- `citations.json`: one verbatim statement quotation for every node used in every proof step.
- `searches.jsonl`: actual searches recorded by the prescribed msearch command; their results are preserved in the item's appended `mathlib_searches`.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean files or compilation commands.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag and for projectivity, graph and finite-extension terminology found no declaration giving this whole statement. The project has `IsHProjective.isProper` and the projective-space closed-immersion lift, but these do not supply projectivity after the finite change of constants or the relative-Proj/free-bundle comparison. Properness alone is not an attachment of the item.

## Literature

WANTED: none. I read the local Stacks sources: morphisms.tex Tags 01W8 (definition-projective), 0B3I (lemma-finite-projective), 087S (lemma-projective-over-quasi-projective-is-H-projective), 01WE (lemma-H-projective-composition), 0C4Q (lemma-projective-permanence) including its actual graph factorization, 01WF (lemma-H-projective-base-change), 01QR (lemma-base-change-closed-immersion), 01QS (lemma-composition-closed-immersion), and 01WC (lemma-locally-projective-proper); schemes.tex Tag 01KR (lemma-fibre-product-after-map); constructions.tex Tag 01NF (definition-projective-space) and its following relative-Proj identification, and Tag 01O3 (lemma-relative-proj-base-change). The ampleness criterion in the definition node was checked against the one-point scheme Spec k. There are no new-node sources to check.

## Corrections and scope

The item was unsplit with an empty proof. Its text cited `def-weil-field`, `def-pc-field-extension` and `def-weil-closed-immersion` without listing them in `stmt_deps`; these edges were added. No statement dispute or mathematical correction was necessary. The full statement, including the specific pair (i,c), arbitrary base change, both projectivity conventions and empty cases, is retained.

I read the chapter and unit records and SETUP's three levels. This is the generic geometric input for projectivity of the final alteration in the recorded direct-image proof (3); it does not replace that unit's alteration or finiteness route. `blueprint_refs.py ancestor` reports None, consistent with the existing `blueprint.from` recording an added input without an imported ancestor. Searches of the whole imported blueprint for projective graphs, closed graphs, finite projectivity and the relevant tags found no equivalent full statement. The unrelated graph-closure/quasi-finite node does not assert it. I preserved `from`, with its already specified place, and recorded `same_as: []`.

## Not duplicates

No new nodes were introduced. I reused the finite-projective-bundle, bundle-to-H-projective, H-projective-composition, fibre-product closed-immersion, closed-immersion base-change and composition, projective-space pullback and free-bundle comparison nodes. In particular, `lem-per-h-projective-permanence` was found and read, but its statement gives existence of a relative embedding rather than identifying the required pair (i,c). I wrote the graph argument from the existing closed-immersion tools rather than assuming this identification from that node's proof.

## Review by Q101

I checked delivery-errors B through E with the item, every cited node statement and the local Stacks passages open. The statement introduces its field extension, source, target and map; all named notions have definition dependencies. No new unsplit lemma contains a proof because none was created. The item's proof uses actual theorem nodes for the non-elementary facts, not bare tags. Its tags and labels identify the local sources. Each of the seven steps is shorter than 2000 characters. The new proof does not hide the item or one of its clauses inside a new node.

Step 1 uses the spectrum definition's one-point assertion, the finite-morphism definition's affine finite-module criterion, and the actual absolute ampleness definition. The hypotheses suffice: F is finite dimensional over k, and the only target opens are empty and the whole one-point spectrum. The section 1 of the trivial line module has the required affine nonvanishing locus. This is an elementary specialization of the definitions, not a new theorem about ample sheaves on general affines.

Step 2 uses exactly the statement of `lem-trf-finite-projective-bundle` for finite u, then the statement of `lem-trf-projective-bundle-to-h-projective` for the ample base Spec k. I checked that the latter requires an ample sheaf on its target, and supplied it before applying it. No ampleness or quasi-projectivity of S is inferred. Step 3 uses the given F-projective embedding, `def-kun-projective`, and precisely the two-H-projective-morphisms hypothesis of `lem-trf-h-projective-composition`. This gives a single integer N and an embedding over k, without separability.

Step 4 uses the separated clause of `lem-weil-pbc-fibre-product-change-of-base-closed-immersion` with X=R, Y=T=S, f=c, g=id and h the k-structure on S. Its statement actually asserts that induced morphism is closed. The domain identification R x_S S = R is written as inverse maps by projections, so the resulting morphism is the graph, including the correct base Spec k. The fibre-product and closed-immersion definitions justify the identification and invariance under an isomorphism.

Step 5 uses exactly `lem-weil-pbc-closed-immersion-base-change` and `lem-weil-pbc-closed-immersion-comp`, with the pullback square explicitly identified by inverse projection maps. `lemma-nagata-projective-space-base-change-pullback` states the ambient isomorphism for every coordinate set and every base morphism; it applies to {0,...,N}. Both components of the composite are computed, proving that the particular map (i,c), not merely some embedding, is closed.

Step 6 again uses the arbitrary-morphism closed-immersion base-change statement, the fibre-product universal property and the same projective-space pullback statement. The projection formulas identify its source with R x_S S' and its structural morphism with c'. No theorem with a flat or Noetherian base-change hypothesis is used. `def-kun-projective` then gives the first projectivity convention with the same N.

Step 7 uses the full over-the-base isomorphism of `lem-trf-free-projective-bundle-base-change-space`, not a definition mistaken for a comparison theorem. The finite free standard basis satisfies the finite-type/quasi-coherent criteria in `pqf-def-coherent`. This provides exactly the sheaf required in `def-trf-projective-bundle-morphism`; the obtained bundle projectivity is precisely the hypothesis of `lem-trf-projective-bundle-proper`. Closedness is unaffected by the ambient isomorphism, as is immediate from the closed-immersion definition. The equality of the free-bundle ambient space with P^N is thus justified separately from projectivity terminology.

For small cases I checked F=k and N=0, R empty, S or S' empty whenever the maps exist, and purely inseparable finite F/k in positive characteristic. F=k reduces the constants map to the identity; a nontrivial inseparable extension is still finite as a module, so Step 2 applies unchanged. Empty base changes give empty closed subschemes. No argument uses points of R or nonempty fibres. The proof also applies to arbitrary separated S without a global ample sheaf. The necessity of separatedness is confined to the graph step, as in the source. All non-definition tool uses from other units are declared in `split_report.tool_uses`; they are generic geometric facts absent from the constructible-functor unit, not changes to its route. No maintainer-owned fields were changed.

Mathlib searches were run through msearch only. LeanFinder's two phrasings yielded Proj properness/separatedness and then linear projectivization/projective-module results; LeanSearch yielded closed-immersion definitions. These do not assert the combined result or a one-line specialization of it. Loogle returned no hits, and the prescribed source grep returned no projectivity/cancellation matches in Mathlib/AlgebraicGeometry. The inherited search records are retained and the actual fresh queries are appended, without inventing searches or treating unavailable services as no matches.

## Unfinished work

None within the one-level split. The reused statement-only free-bundle comparison remains its own existing DAG item. This delivery does not claim to have proved that node in Lean.

## Repair of return L (2026-10-23)

The returned delivery was `d30dd8615e6`. I continued the retained sandbox rather than reconstructing or discarding its proof, citations or search log. The return identifies a disagreement between the side completion and the live DAG, not a rejected mathematical argument. In the current shared repository the item is `unsplit`, with no proof and no `reviewed` record. Its statement, source, creation metadata, chapter, unit and blueprint provenance agree with the retained item. Comparing every field shows that the retained delivery changes only `status`, `stmt_deps`, `proof`, `proof_deps`, `proof_origin`, `mathlib_searches` and `split_report`, all split-owned fields. The delivery tool rebuilt the retained split on its freshly fetched current DAG and the initial required dry run exited successfully at `b3cde61d12a`.

I re-read all ten statement dependencies and all seventeen distinct proof dependencies in the current DAG (overlap counted only once when reading). Every dependency exists and is unmerged. I compared each of the 23 step/node citation entries against the current statement: every retained quotation is still verbatim, so no citation replacement or dependency substitution is needed. In particular the finite-to-bundle, ample-base-to-H-projective and composition hypotheses still justify Steps 2–3; the separated fibre-product theorem still supplies precisely the graph in Step 4; and the free-bundle comparison remains the existing statement-only node, with an isomorphism over an arbitrary base. No current definition licenses silently conflating the relative-Proj and base-change projective spaces.

To make the assembly with these current interfaces explicit, I revised Step 7 to name the comparison theta and the actual bundle embedding theta inverse composed with j'. Its structural-map equation follows directly from the quoted identity q theta = p. This verifies that the new bundle embedding has structure morphism c', rather than merely identifying its ambient schemes. The full statement and the seven-step route remain unchanged. I again checked the local Stacks statements and proofs listed above, including the distinction between projective and H-projective in Tag 01W8, the ample-base hypothesis of 087S, the closed-graph factorization of 0C4Q and arbitrary base change in 01WF/01O3. The small and empty cases in the original review continue to apply. The current Lean search supplies no full attachment. All earlier Mathlib searches and their recorded results are retained; their mathematical search questions have not changed, so they were not repeated.

This repair updates the split and this review, then reruns the required server dry run before pushing. The side-completion promotion itself is maintainer-owned; this delivery supplies the reconciled split on the current DAG through the authorized delivery tool.
