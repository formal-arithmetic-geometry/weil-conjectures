# Stage-1 split: lem-coef-exponential-dependent-product-representation

## Files written

- dag/nodes/sec-six-functors/lem-coef-exponential-dependent-product-representation.json: statement, split; no Mathlib match for the full quasicategorical claim. Five proof steps use existing nodes only.
- citations.json: one exact statement quotation for each cited node in each step.
- searches.jsonl: actual msearch.py queries and result digests; corresponding records appended to the item, retaining every inherited query.
- report.md: this report replaces the temporary missing-input report after the shared snapshot refreshed.

New nodes: 0. New Mathlib leaves: 0. The statement, statement dependencies, source, blueprint ancestry, Lean audit and inherited search records are retained.

## Attachments

None. Searched the project WeilConjectures tree for the exact blueprint ID and for exponential, dependentProduct, internal Hom, cartesian closed, exponentiable, sectionsCurry and toOverSectionsAdj. The exponential hits are analytic/zeta or Fourier statements; internal Homs are ordinary derived-category or cochain-complex constructions. No project declaration states this claim about arbitrary locally small quasicategories and full coherent mapping spaces.

## WANTED

WANTED: archival copy of Kerodon Proposition 7.7.3.13, Tag 05UT, for lem-coef-exponential-dependent-product-representation. Read online at https://kerodon.net/tag/05UT. This is a Kerodon tag, not a Stacks tag; no matching Stacks theorem is claimed. The explicit pullback formula is the worker's argument, so proof_origin.by is agent.

## Audit of the input and route

The sandbox initially held only the brief markers. The initially stale shared snapshot did not yet contain the assigned node; one required deliver.py --no-push invocation fetched the updated snapshot and then exited because the sandbox had no node files. After that fetch the item was present and I continued from the authoritative JSON. That transient input problem is resolved.

Read the chapter sec-six-functors and unit sk-prop-sf-biduality-general, the ancestor prop-coef-integral-exceptional-adjoint, and the parent lem-coef-space-universal-colimits. This item supplies exactly the exponential pullback representation used in the parent's steps 3–4, before the iterated-slice identification. The ultimate blueprint place is the ancestor's second proof paragraph, finite-level mapping adjunction before R lim. The proof uses abstract mapping-space foundations and changes no geometric route. It cites no SGA source. No unit realization fields are changed: this item is an auxiliary lemma, not a unit key statement.

No statement dispute was found. Kerodon 05UT assumes all finite limits to prove existence of a global adjoint; this item assumes the particular terminal object, products, exponential adjunction and pullback it needs. The proof therefore uses only those specified objects and does not import the source's stronger ambient finite-completeness hypothesis. Its naturality is on the full subcategory of arrows for which the pullback exists.

## Mathlib and duplicate searches

Ran leanfinder twice with the item's own claim in mind, loogle for CategoryTheory.Over.toOverSectionsAdj, grep for toOverSectionsAdj|sectionsCurry|homotopyFiber|mappingSpace in CategoryTheory/LocallyCartesianClosed, and leansearch for the representing pullback claim. Read every returned hit and the main candidate's source at Mathlib/CategoryTheory/LocallyCartesianClosed/Sections.lean:38–49,68–71,82–101,138–173. The ordinary sections construction is a close analogue, but its Category and CoreHomEquiv types give bijections of hom sets, whereas this item concerns coherent mapping spaces and their homotopy fibers in arbitrary quasicategories. The second semantic phrasing returns truncated homotopy-category products, which likewise do not supply the theorem. No match was declared; actual query strings and digests are retained in searches.jsonl and the item's added search records.

Searched the whole DAG and blueprint by exponential, mapping spaces, and the source tags 05UT and 05V1; ran blueprint_refs.py ancestor and both blueprint search queries. The blueprint exponential hits concern analytic power series, zeta functions or Fourier sheaves. The existing item is an auxiliary descendant of prop-coef-integral-exceptional-adjoint, not an alternative imported blueprint statement. same_as remains empty. Existing general mapping-space nodes supply all supporting facts, so nothing new was created.

## Not duplicates

No new nodes; no new/existing same-tag pairs to distinguish. The iterated-slice mapping node and the space-universal-colimits parent use or complement this representation rather than duplicating its general exponential pullback formula.

## Review by Q21

I read Kerodon 05UT's statement and complete proof online. Its route represents maps from the product-to-slice functor using exponentials and pullbacks; our proof spells out that representing object directly on full mapping spaces. I checked every citation against the actual existing node statement rather than its proof, with exact quotations in citations.json.

Step 1 uses lem-coef-infinity-yoneda-presheaf-limits for preservation of this existing finite-span limit by Map(T,-), including naturality. It does not need existence of arbitrary limits in C. The point into Map(T,1) is a weak equivalence because 1 is terminal. lem-coef-kan-homotopy-pullback-invariance applies to a strictly commuting map of spans, with that point inclusion and two identity maps; it removes precisely the contractible terminal-map coordinate. lem-cbc-enhanced-functor-cone-calculus states that the mapping spaces are Kan, so the invariance lemma's Kan hypotheses hold.

Step 2 is elementary substitution in the adjunction equivalence already assumed by the item: naturality in z gives the postcomposition square, and naturality along T to 1 sends the transpose of the identity to the projection. No additional currying theorem is hidden here. The formulas apply to the coherent equivalence, not only its components.

Step 3 uses the forward direction of lem-coef-spaces-homotopy-fiber-detection. Both its horizontal maps are the assumed adjunction equivalences; its square is equipped with the actual naturality homotopy. Thus its full homotopy-fiber comparison is an equivalence, even if the fiber is empty. The final path from the transposed section to the projection was proved in step 2. The explicit path composite records all compatibility data.

Step 4 specializes the cone-category mapping formula of lem-cbc-enhanced-functor-cone-calculus to a point diagram with value a. Its two cones are exactly the projection and p. This supplies the full slice mapping space as the same homotopy fiber. That generic node is in another unit, so it is declared in split_report.tool_uses; it is a foundational tool, not a replacement for this unit's route.

Step 5 uses lem-coef-parametric-universal-arrows with G the product-to-slice functor and D_0 the full subcategory of arrows having the specified pullback. The universal arrows are actual evaluation maps with the pullback triangle. The required universal-arrow equivalence is exactly what steps 1–4 proved, including the formula on a test map. The cited theorem explicitly supplies coherent assembly with contractible choice and all simplicial parameters. The representable-limit lemma explicitly supplies naturality in diagrams and test objects. I wrote the action of an arrow p to p' and checked that adjunction naturality matches its evaluated triangle. This avoids assuming an unspecified functorial choice of pullbacks.

Edge checks: for a terminal a, the pullback formula reduces to y and the slice over a is equivalent to C; for p=id_a the pullback is terminal and every displayed mapping space is contractible. In sets, if a is empty then [a,y] and [a,a] are singletons and the sections object is terminal; if a is nonempty and y is empty, both sides are empty except for empty test source. The proof uses homotopy rather than strict fibers, so non-discrete automorphism and higher-path data are retained. No point of a, y, T or a homotopy fiber is assumed. Neither finite completeness of C nor a Kan-fibration property of p is silently used.

Checked delivery-errors B–E: no new unsplit statements or hollow definitions, no relabelled clauses, no unrecorded Mathlib queries, no missing non-elementary cited fact, and no citation to a definition as a substitute for a theorem. A recursive dependency inspection found no path from the supporting nodes back to the item. All five steps are shorter than 2000 characters; the longest is the final coherence step at 1571 characters. The statement is unchanged. No Lean writing, compilation, Lake command, direct git command, shared-project edit or launcher edit was performed.

## Unfinished work

None in the mathematical split. The independent maintainer review is still required after delivery.
