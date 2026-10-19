# Worker report: lem-coef-infinity-cartesian-mapping-criterion

## Files written

- dag/nodes/sec-six-functors/lem-coef-infinity-cartesian-mapping-criterion.json: statement node, split into ten steps; no Mathlib match.
- citations.json: one verbatim statement quotation per cited node per proof step.
- No new DAG nodes, no new definitions, and no Mathlib leaves. The sandbox also retains the actual searches.jsonl and the item-specific generation script; neither is a project change.

## Attachments

None. I searched the entire read-only slopmaster2 WeilConjectures tree for the blueprint id and quasicategory/Cartesian-edge terminology. No project declaration states this criterion. The ordinary-category fibered results found by semantic searches do not establish it.

## WANTED

WANTED: Jacob Lurie, Higher Topos Theory, Proposition 2.4.4.3, printed pp. 131-132; Proposition 2.1.2.1, Lemma 2.1.2.3, Lemmas 2.1.3.3-4 and Lemma 2.4.4.1, for lem-coef-infinity-cartesian-mapping-criterion. I read the Harvard-hosted author PDF online. No archived HTT is listed or available under literature/. The node is consequently marked proof_origin.by = agent, with the blueprint ancestor as its local document. No download or literature modification was made.

## Findings and corrections

The inherited statement is true and unchanged: it requires only an inner fibration between quasicategories and a specified edge. It does not assume a Cartesian fibration or other Cartesian lifts. Its empty proof has been replaced with the slice construction and explicit horn/fiber tests of HTT 2.4.4.3.

The source explicitly warns that the square in the homotopy category alone is insufficient: the strict slice square specifies the commutation data. Steps 7-9 retain that representative and write the triangle prism comparing it to postcomposition on the specified right-pinched spaces. I did not silently substitute an arbitrary commutation homotopy or appeal to mere commutation on components.

The current blueprint ancestor's paragraph 2 concerns coefficient adjunction; this foundational tool serves its arrow-target Cartesian-fibration branch through the existing blueprint.from chain. I read the unit sk-prop-sf-biduality-general and the sec-six-functors chapter records, the ancestor proof in the current main-20261015 snapshot, and the project goal and sync policy. No unit statement, target statement, coefficient category, or route was changed.

Mathlib searches were run only through msearch.py and are logged. Loogle SSet.Quasicategory returned horn-filling definitions and edge homotopies. The algebraic-topology grep returned no Cartesian/mapping criterion. Two LeanFinder phrasings returned Quillen fibrations and ordinary-category fibered morphisms; their displayed types concern those objects, not the quasicategorical assertion. LeanSearch returned a rate-limit error, recorded as unavailable. I retained all inherited search records and appended the actual queries of this run.

## What remains unfinished

Nothing in this item's one-level split. The existing foundational dependencies remain separate work items. Delivery checks are run after this report is written.

## Not duplicates

No new nodes are created. The whole DAG and blueprint search for the mapping criterion returned no imported blueprint statement to attach to. The existing cocartesian criterion is the opposite orientation; it was read for comparison but is not cited, nor is its proof treated as a statement. The Cartesian mapping-fiber lemma only tests vertices in the source fiber and assumes a Cartesian edge, so it is not the converse criterion here. Existing slice, fibration-fiber and path-comparison nodes supply all genuine auxiliary results. I checked their transitive statement/proof dependencies; none reaches this item.

## Review by N4

I read HTT Proposition 2.4.4.3 on printed pages 131-132 directly in the author PDF, including its final warning and strict square, and its cited slice and fibration statements. The source's objects Y,Z,X correspond to this item's x,y,z. All its hypotheses are exactly the inner fibration and quasicategories already in the item. The source uses the same right-pinched mapping simplicial sets as def-cbc-enhanced-diagrams-cones. No Stacks tag supplies this assertion, and no SGA source is used.

Step 1 uses the actual statement of lem-coef-infinity-slice-right-fibration: it allows any diagram K, hence both the specified edge and its vertices, and its fiber over a vertex is the right-pinched mapping space in the one-vertex case. For the edge diagram, the right-fibration-over-a-Kan-base assertion of lem-cbc-right-fibration-space-fiber makes the slice fiber Kan. All joins, projections and fibers are degreewise, with a constant whole initial face.

Step 2 uses the pushout-join clause of lem-coef-infinity-anodyne-cocones, rather than its unrelated cocone equivalence clause. The first inclusion is a generating right horn, the second a monomorphism, and p is an inner fibration. I wrote out why inner-horn lifting extends through the defining saturated operations. Thus the quoted statement says precisely what this application needs; no relative slice theorem is assumed without proof.

Step 3 is elementary face bookkeeping from the two cited definitions. With m+1 initial vertices and the final two vertices x,y, the union is exactly the final outer horn. I checked m=0 explicitly: its two edges include the specified s and the given arrow into y, and a lift supplies the missing arrow into x. This includes the empty-boundary test required by the trivial Kan definition.

Step 4 uses the exact Kan-fibration assertion of lem-coef-infinity-inner-mapping-fiber, with endpoints z,y and images p(z),p(y). The target pullback is Kan because its projection is a pullback of that Kan fibration onto the Kan slice fiber from Step 1. The stated right-fibration result then applies to phi_z. I wrote the elementary pullback and total-space horn filling rather than creating redundant nodes.

Step 5 uses the full equivalence among weak equivalence, trivial fibration and contractible vertex fibers in lem-cbc-kan-fibration-fiber-criterion. The converse applies lem-coef-right-fibration-contractible-fibers, whose statement imposes no quasicategory condition on its target. Every vertex of Q has a definite source z, so the required fibers are exactly those tested. In particular no nonemptiness hypothesis was smuggled in: contractibility forces nonemptiness where it is needed.

Step 6 uses lem-coef-kan-pullback-path-comparison with the right vertical map, whose Kan-fibration hypothesis was established in Step 4. The square commutes strictly, so the comparison uses constant paths. Two-out-of-three is just the corresponding assertion for bijections of components and isomorphisms of homotopy groups.

Step 7 writes the full inner-horn calculation proving that restriction to x is a trivial Kan fibration; it is not an uncited general restriction theorem. The source node def-cbc-enhanced-diagrams-cones provides the inner horn fillers, def-weil-pbc-trivial-kan-fibration identifies all boundary tests, and lem-weil-pbc-trivial-kan-homotopy-equivalence supplies an actual section and homotopy inverse. That last generic simplicial-set tool lies in another unit, so its use is explicitly declared in split_report.tool_uses. This does not replace a route step of this unit.

Step 8 uses the stated triangle-space equation of lem-coef-infinity-mapping-composition and the actual natural inclusion and homotopy equivalence in lem-coef-infinity-pinch-comparison. The monotone prism map has exactly the three claimed restrictions. Applying p to it gives the same construction on B on every simplex, so the chosen coherence is retained. Step 9 uses the strict-cospan invariance statement of lem-coef-kan-homotopy-pullback-invariance only on a strict natural pinch comparison, where its two equations really hold. The remaining replacement of the left corners is the explicit roof presentation of composition, with its triangle witness from Step 8, as prescribed by the source. Step 10 only combines the previously proved equivalences.

I opened every cited node's statement and copied those statements verbatim into citations.json; none is cited for an assertion hidden only in its proof. I checked the item in the terminal-category example, for p the identity, for p:E to a point (where the criterion recognizes equivalences), and for nerves of ordinary categories (where the mapping squares become the unique-factorization Cartesian condition). Degenerate s is permitted throughout. Empty mapping spaces are permitted; m=0 is retained in both boundary arguments. These checks found no statement dispute.

I checked delivery-errors B-E against the files: no statement-only node contains a hidden proof because no new node is needed; no clause of the item is moved to a new node; no circular dependency is introduced; statement and proof dependencies are distinct and proof_deps is the exact union of uses. All non-elementary claims are either cited or are the displayed direct horn/prism calculations. Every proof step is shorter than 2000 characters, and I also checked that their separation does not hide a general comparison lemma. The auxiliary comparisons already have their own cited DAG nodes. Nothing was written to the shared repository, live Lean sources, or launcher, and no compiler or build command was run.
