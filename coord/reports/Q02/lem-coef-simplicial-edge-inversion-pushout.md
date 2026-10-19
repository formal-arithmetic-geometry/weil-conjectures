# Worker report: lem-coef-simplicial-edge-inversion-pushout

Group Q02, stage 1, 2026-10-17. Direct delivery under the dispatcher brief; no further worker or agent was started.

## Files written

- dag/nodes/sec-six-functors/lem-coef-simplicial-edge-inversion-pushout.json: statement unchanged; six proof steps; status split. Existing source, provenance, ancestry and searches retained.
- dag/nodes/sec-six-functors/lem-coef-inverse-gadget-categorical-contractibility.json: new statement-only node; status unsplit; Mathlib searches found no match. It states categorical contractibility of the explicitly specified quotient Q, tested on entire functor categories.
- citations.json: fourteen verbatim statement excerpts, one for every step/node citation.
- report.md: this report.

## New nodes

lem-coef-inverse-gadget-categorical-contractibility: statement, unsplit, no Mathlib match after the six recorded searches; its only statement dependency is def-cbc-enhanced-diagrams-cones.

## Attachments

None. I searched the whole read-only slopmaster2 WeilConjectures tree for the item tag, edge inversion, inverse gadget, simplicial localization and quasicategory keywords; no matching project declaration appeared. The same finite-gadget searches in the exact master reference tree found no matching declaration. Master sorry declarations would not qualify as finished attachments. No Lean was written, opened through a compiling tool, compiled or built.

## WANTED

WANTED: an archival copy of Kerodon Corollaries 6.3.2.7-6.3.2.9, tags 05ZJ, 05ZK, 05ZL, and Remark 6.3.1.15 (05ZC), for this item and lem-coef-inverse-gadget-categorical-contractibility. Read online at https://kerodon.net/tag/05ZJ, https://kerodon.net/tag/05ZK, https://kerodon.net/tag/05ZL and https://kerodon.net/tag/05ZC. I also read Proposition 6.3.2.4 (05ZD), Example 4.5.5.12 (01FJ) and Corollary 6.3.2.5 (05ZG). These are Kerodon identifiers, not Stacks tags. No Stacks result states this quasicategorical inverse-gadget theorem. The proof is marked agent-written because these sources are not archived in literature/; no literature files were downloaded or changed.

## Audit of the imported material

The item was an unsplit statement with no proof or project attachment. Its statement agrees with 05ZL after expanding Q and e from 05ZJ/05ZK; it requires no correction. In particular the edge is 12, not 01; Q has two vertices, and the edges collapsed are 02 and 13 separately. Neither the source nor the item assumes C or D is quasicategorical. The monomorphism required for the pushout argument is the coproduct of e, not the map enumerating the edges in C. That distinction permits degenerate selected edges and coincident endpoints in C.

I reused lem-coef-localization-monomorphic-pushout instead of creating a second categorical-pushout or localization-under-cobase-change node. Its statement is about maps of spans, so step 6 spells out both spans and all three vertical maps, rather than silently citing a different theorem. The new child concerns Q alone and has neither C nor W nor the arbitrary attachment pushout. It is therefore a smaller input, not the item with a new label or the singleton-edge localization clause moved into a child. The interval and coproduct calculations remain proof steps rather than new elementary nodes.

The chapter and unit records were read and left untouched. The unit has no recorded proof steps and this item is an auxiliary descendant, not its key statement. The existing ancestry records the localization construction beneath prop-coef-integral-exceptional-adjoint; this split continues that auxiliary route. No SGA source was used.

## Searches

The sandbox was empty of node, report and search records at start. Ten actual msearch.py queries were run and their results read. Six concern the new quotient-contractibility child and four the item; every new search entry is copied from the resulting searches.jsonl record with the exact tool and query. Both semantic phrasings of the child were tried. Loogle's SSet/categorical-equivalence and SSet/localization queries returned no hits; both grep phrasings for the child and the item grep returned none. All services used were available. Semantic hits concern terminal standard simplices, ordinary simplex categories and nerves, ordinary category localization, Quillen/Kan generators, skeleton/coskeleton, ordinary horn pushouts, and colimits of simplicial sets. Their signatures do not assert a categorical equivalence for this quotient or the coherent edge-localization property. I read Mathlib/CategoryTheory/Localization/Predicate.lean:45-58 and AlgebraicTopology/Quasicategory/Basic.lean:35-57 to check the distinction. There is no Mathlib leaf in this delivery.

Before creating the child I searched the entire DAG for its proposed id, 05ZJ/05ZK, inverse gadget, categorical contractibility, localization pushouts and the corresponding project source terminology. I ran blueprint_refs.py ancestor on the item and whole-blueprint searches for inverse gadget, inverse-gadget, 05ZJ, three simplex, contractible and localization. No blueprint statement states the new child. Its blueprint.from has the recorded nearest ancestor and the item prepended to the existing via list, with the exact supporting source place; same_as is empty.

## Not duplicates

lem-coef-inverse-gadget-categorical-contractibility vs lem-coef-simplicial-edge-inversion-pushout: the child only states the equivalence E -> Fun(Q,E) for the finite quotient Q; the item localizes an arbitrary C at any collection W by attaching copies of Q, and its steps prove the inverse-edge, interval, coproduct and attachment arguments.

lem-coef-inverse-gadget-categorical-contractibility vs lem-coef-simplicial-localization-existence: the latter constructs a strictly functorial quasicategorical localization preserving filtered colimits, using the item as an input; it does not state categorical contractibility of Q. The child has no localization construction or filtered-colimit clause and does not depend on that existence node.

lem-coef-inverse-gadget-categorical-contractibility vs lem-coef-quasicategory-invertible-interval: the existing statement is about the infinite nerve J of the walking isomorphism, endpoint evaluation and the lifting of homotopy-category isomorphisms. The finite degreewise quotient Q is a different simplicial set and is not assumed quasicategorical; identifying its categorical type is precisely the new assertion.

## Review by Q02

I read the complete B-E checklist in delivery-errors.md and checked the statement and every cited node's statement, not its proof, against the delivered argument. For the item I read Kerodon 05ZL and the full 05ZJ/05ZK proofs it invokes. For the new child I read 05ZJ: its quotient is exactly the disjoint-edge collapse specified here and its conclusion is categorical equivalence to a point. The whole-functor-category interpretation agrees with the existing lem-coef-joyal-functor-equivalence-test, whose statement I also read. The child contains only its statement, searches and metadata, with no hidden proof sketch or proof dependencies.

Step 1 uses def-cbc-enhanced-diagrams-cones for standard simplices and simplicial maps. I checked injectivity in every degree, rather than relying only on the two distinct vertices: nonconstant 12 strings are in neither collapsed subcomplex; constant strings map to the two different quotient vertices. Taking a coproduct preserves this injection component by component. There is no injectivity claim about the arbitrary attaching map to C.

Step 2 uses lem-coef-infinity-mapping-composition for the homotopy category, the two triangle relations, associativity, and the equivalence-edge criterion. I opened its statement and checked all four facts are stated. The quotient faces give ba=1_A and cb=1_B; the calculation a=cba=c proves that b has a genuine two-sided inverse in hE. The cited criterion turns that into the exact inverse-triangle notion in the definition node. Full-subcategory factorization holds on every vertex of every parameter simplex.

Step 3 uses lem-cbc-enhanced-functor-cone-calculus for the quasicategory of arrows and its full subcategory, and lem-coef-infinity-pointwise-equivalences twice. Both statements apply to arbitrary small shapes; no Kan or nonemptiness assumption on E is introduced. I checked the actual min(s,t) formula: at t=0 it is the constant source arrow, at t=1 it is the given arrow, at s=0 its transformation component is the identity, and at s=1 it is f. The universal evaluation formula retains all diagram parameters and simplicial operators. The full subcategory retains the inverse and triangle witnesses because every one of their vertices is one of these allowed objects. Thus the step proves interval localization directly and does not hide it in a child lemma.

Step 4 uses exactly the new child's conclusion that the actual constant map k_Q is a coherent equivalence. The source and target of its e are those of steps 1-2, so r k_Q=k_1 strictly. I wrote the quasi-inverse s=k_Q u_1 and both inverse equations; this avoids replacing the whole functor-category property by a claim about cores, objects, or ordinary homotopy categories. The localization definition cited is exactly the factorization-and-coherent-equivalence property obtained.

Step 5 uses the functor simplicial-set and localization definitions. The coproduct-to-product formula is a degreewise bijection with all simplicial operators, and the product inverse and triangle witnesses are coordinatewise ones. This is an elementary construction from step 4, not an unquoted theorem about arbitrary infinity-categorical limits. It includes an empty product and allows W to contain degenerate edges.

Step 6 uses lem-coef-localization-monomorphic-pushout. I opened its full statement and checked each hypothesis against the displayed two spans: u_0 is the identity, v_0 is i, p_0 is the coproduct localization from step 5, p_01 and p_1 are identities localized at the empty set. Its edge-compatibility assumptions have empty left sides. Its conclusion inverts exactly f(V)=W and applies to arbitrary simplicial sets and noninjective remaining legs. The source pushout identification with C follows directly from gluing along the identity; the target is exactly the degreewise pushout in the item. The mapping-composition, pointwise-equivalence and monomorphic-pushout inputs and the new child have the item's unit. The enhanced definition and functor-category calculus come from sk-prop-sf-cbc; they are existing foundational inputs, and the server route check accepted these citations without an off-route exception.

Small cases checked: W empty gives D=C and j the identity; C empty forces W empty; a singleton nondegenerate edge in C gives the one-copy attachment; a selected degenerate loop still has a noninjective attaching map but is covered by step 6; repeated endpoints or different selected edges sharing endpoints cause no monomorphism failure because i is the monomorphism. For Q itself the vertices stay distinct and its distinguished edge goes from the second collapsed vertex to the first. For E empty both E and Fun(Q,E) are empty (Q has vertices), so the child asserts an equivalence of empty categories, not an inhabitant. For E the nerve of an ordinary category, the two triangle relations reduce to ordinary left/right inverse equations. For E=Delta^0 the functor categories and contractions are terminal. These tests revealed no statement dispute.

No proof step exceeds 2000 characters (lengths 582, 815, 1112, 791, 812, 1000). I checked the formulas even though the long-step trigger does not apply. Every non-elementary imported fact has a node, all cited statements say what is taken from them, and citations.json excerpts were checked for literal containment. The only new node is the non-elementary finite-gadget input; no elementary, duplicate or item-clause node was created.

## Unfinished work

No part of the item's split remains unfinished. The new supporting theorem is intentionally unsplit, as required for a one-level stage-1 delivery. The server dry run completed successfully: OK (not pushed), commit 1dde7d9565, preflight passed. A final dry run checks the final sandbox contents before the authorized direct push.

## Validation

The required deliver.py --no-push command exited 0 and printed OK; the server preflight, including check_dag.py and review_split.py, passed. Only the permitted remote delivery tool ran these checks. No tool workaround, global build, compiler or Lake invocation was used.
