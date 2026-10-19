# Stage-1 report: lem-coef-enriched-bar-projective-replacement

## Files written

- `dag/nodes/sec-six-functors/lem-coef-enriched-bar-projective-replacement.json`: statement, now split into six steps. Actual logged LeanFinder (two formulations), Loogle, LeanSearch and source grep searches found no Mathlib match for this enriched bar diagonal. Existing search records were retained and the Q147 records appended.
- `citations.json`: 13 step/node citations with verbatim excerpts checked against the current node statements.
- `report.md`: this report. No new nodes; no Mathlib leaves introduced. The sandbox also retains the actual search log and its local writing script.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint id, enriched bar, and projective cofibrancy found no exact declaration. The upstream master source was also searched for these terms and was not treated as proof evidence. The item has no own Lean-audit declaration to inspect.

## Sources wanted

WANTED: Daniel Dugger, *A Primer on Homotopy Colimits*, https://pages.uoregon.edu/ddugger/hocolim.pdf, §§3.1–3.4, Proposition 9.11, Remark 9.12 and §19.1, archival copy for this item. Read these passages online; no download to the repository was attempted.

WANTED: Jacob Lurie, *Higher Topos Theory*, https://www.math.ias.edu/~lurie/papers/HTT.pdf, Proposition A.3.3.2 and Remarks A.3.3.4–A.3.3.5, archival copy supporting the existing simplicial projective model input. Read online. No Stacks tag states the enriched homotopy-theoretic assertion, and none is fabricated. No SGA source is used.

## Problems found and corrections

The statement is unchanged. Dugger gives an ordinary-diagram construction, so his proposition is not presented as an enriched theorem. The missing enriched argument is supplied explicitly: isolate the free final mapping factor, compute the degeneracy colimit on its coefficients, use the actual projective lifting test, and invoke the existing general realization result. Merely knowing that the bar levels are objectwise cofibrant would not prove this assertion. Neither would applying the latching-degenerate-subset theorem to the coefficients ending at a fixed vertex: those coefficients have degeneracies but do not in general have all faces preserving that endpoint. The proof instead checks their degeneracy overlaps directly.

I retained the original statement dependencies, provenance, blueprint ancestry and source. The nearest blueprint ancestor is `prop-coef-integral-exceptional-adjoint`, whose paragraph 2 uses the coherent middle adjunction. This item supplies the inherited derived coend branch's free replacement; it does not replace the geometric unit route. The item is not a unit's key node, so no unit record is changed.

## Unfinished work

No mathematical part of this one-level split remains. No helper statements were created. The archived-source requests remain for the maintainer. All generic inputs used here already have DAG nodes in the same unit.

## Not duplicates

No new nodes. Whole-DAG statement searches for Reedy, latching, projective cofibrancy, free bar and simplicial tensors found the existing `lem-coef-reedy-realization-prism`, `lem-coef-reedy-model-structure`, `lem-coef-simplicial-projective-model-calculus` and `lem-coef-kan-quillen-right-proper`; these are cited directly. Whole-blueprint searches for enriched bar projective cofibrancy, projectively cofibrant, bar resolution, bar and realization found no other blueprint statement of this item. `blueprint.same_as` remains empty. The ordinary framed-diagram resolution has a different source category and cosimplicial frame; it is not used as an enriched result.

## Review by Q147

I read the item, its parent derived-space-module co-Yoneda statement, the unit/chapter records, the ancestor proof, the stage-1 brief and delivery-errors B–E. For the mathematical source I read Dugger's forward-bar variant in Remark 9.12, its reference to Proposition 9.11, the realization coequalizer and skeletal attachment in §3, and the simplicial-model tensor discussion in §19.1. I read HTT A.3.3.2 and A.3.3.4–5 for enriched projective models and free diagrams. The enriched latching calculation is my argument, so `proof_origin.by` is `agent`. There are no new-node sources to review.

Step 1 uses the free/evaluation adjunction and simplicial projective structure stated by `lem-coef-simplicial-projective-model-calculus`, and the simplex/simplicial-set definitions stated by `def-weil-pbc-simplicial-set`. The coefficients omit precisely the final representable factor; $K_0(a)=X(a)$. I checked both the first-face action identity and the final-factor composition identity; the remaining relations are associativity, units and disjoint operations. No Kan condition enters.

Step 2 uses only that simplex definition and the proper-surjection latching definition of `lem-coef-reedy-model-structure`. The coefficient diagrams contain every proper surjection and its factorization maps. At fixed internal degree, deleting prescribed identity slots gives a unique preimage; two presentations have a common refinement obtained by deleting their union. This proves both surjectivity onto the identity union and injectivity of the colimit map. Internal operators take identities to identities, even if they take some nonidentity simplex to an identity, so the union is a simplicial subset. No assertion of a simplicial complement is made.

Step 3 again uses the actual free/evaluation adjunction and the Reedy latching definition. I checked that every degeneracy leaves the final object fixed, including insertion at that last object, and acts identically on its final representable factor. The universal-property argument tests maps to an arbitrary enriched module and so establishes the latching colimit in the correct category. It does not assume a theorem about ordinary diagram latching objects that the cited nodes fail to state.

Step 4 uses precisely the Kan-model assertion that degreewise injections are cofibrations, the projective model assertion that trivial fibrations are objectwise, the free adjunction, and the Reedy latching criterion. The lifting problem is transferred to one in simplicial sets and solved there, then the family of fillers is assembled. This proves projective cofibrancy of the latching maps, rather than appealing to the converse of the cited theorem that evaluation preserves cofibrations. Smallness of $A$ makes all the coproducts small. Choice of a family of lifts imposes no finiteness or nonempty-value condition on $X$.

Step 5 uses exactly the sentence in `lem-coef-reedy-realization-prism` saying that realization of a Reedy-cofibrant simplicial object is cofibrant. Its second Reedy-cofibrant simplicial object can be taken equal to the first; its homotopy/cylinder clauses are not needed. The model structure in the calculus node is explicitly simplicial and combinatorial, hence complete and cocomplete as required. I checked the proof/statement dependency closure of each used non-definition input for a path back to this item: none exists. All four are in the item's own unit; no off-route tool declaration is needed.

Step 6 uses the simplex definition and the calculus node's objectwise tensor. For the coend/diagonal identification I wrote the map on representatives and its inverse, checked the quotient relation, checked an arbitrary internal simplex operator, and checked the enriched action by an arbitrary degree-$r$ mapping simplex. Thus this is an enriched-module isomorphism, not only a bijection on vertices. Transferring a lift along an isomorphism proves the final cofibrancy assertion directly.

For small cases, I checked degree zero (empty latching object), degree one (only identity arrows form the latching part), and degree two (the two identity loci intersect at the twice-inserted chain). A pair of nonidentity inverse arrows is not degenerate merely because its composite is an identity; the proof imposes identities on the displayed factors, so does not make that mistake. I also checked the one-object identity category, where higher coefficient chains are all degenerate and the result is simply the cofibrancy of $X$; the empty category; empty module values; and a simplicial category with non-Kan mapping objects. The argument uses only identity simplices and monomorphisms in the last case.

Against B: the statement is self-contained via its unchanged definition dependencies, no new unsplit nodes contain proofs, TeX uses ordinary single escapes after JSON decoding, and all search entries come from actual runs with actual results. The apparent bar hits are `Rep.barResolution`, a chain projective resolution (source read at Resolution.lean:430–433), and a generic cofibrant-resolution functor, not the item. Against C: I opened all five cited statements and checked every used assertion as described above; citations.json contains exact substrings. Against D: no clause has been moved into a new node, the proof carries the free-coefficient calculation and quotient identification, and no cycle was introduced. Against E: no local Kan, nonempty, endpoint-preserving face, or finite object-set assumption was added. Every step is shorter than 2000 characters; the only non-elementary black boxes are explicitly cited. The elementary steps carry the concrete computations needed for this particular bar, without introducing helper nodes for short adjunction or quotient calculations.

## Dry-run repairs

The first dry run rejected the step-5 realization-cofibrancy quotation as shorter than its 40-character evidence minimum. I replaced it with the full cofibrancy-and-cylinder sentence. I also expanded the projective-model and Reedy quotations so that each gives the precise model/free-adjunction or latching assertion used, rather than a short fragment. All 13 quotations are verbatim current statement substrings and at least 40 characters. A separate finite identity-slot check tested 17,472 pairs of proper identity deletions in chains of lengths 1 through 6 and confirmed their common refinement by deleting the union. This is an additional sanity check, not a replacement for the general proof.
