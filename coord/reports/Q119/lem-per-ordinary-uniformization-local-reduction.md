## Worker report

Files written, all under dag/nodes/sec-deligne-laumon-a1/:

- lem-per-ordinary-uniformization-local-reduction.json: item, statement preserved, seven proof steps, status split.
- lem-per-ordinary-alteration-cover-approximation.json: statement-only ordinary covering-certificate approximation lemma, unsplit; no Mathlib match.
- lem-per-ordinary-henselian-regular-pair-spreading.json: statement-only spreading theorem for a prescribed marked ordinary covering, unsplit; no Mathlib match.

Attachments: none. Searches of lean/WeilConjectures/ for the blueprint item tag, uniformization/uniformisation, quasi-excellence and alterations found no declaration stating the item or either new interface. The existing connected-regular integrality theorem is reused through its existing node, not proposed as an attachment of this item.

WANTED: none. I read the locally archived Illusie–Laszlo–Orgogozo volume, Expose II pp.31,33--34 (4.1.1 and 4.3.3), III pp.35--38,41--45 (finite diagrams, 3.1(i),(ii), 5.1,5.4 and 6.2), and VII p.81 (2.1--2.3). All sources are in the named repository literature directory. There is no SGA citation.

The item itself was not wrong, and neither its statement nor its statement dependencies changed. The potentially misleading neighboring interfaces are prime-to-ell assertions: they cannot be used on an arbitrary ordinary alteration cover. In particular I did not assert that an arbitrary ordinary cover is prime-to-ell for a convenient prime or that a prime exists invertible on every base. The ordinary source explicitly has Proposition III 3.1(ii); this is what the first new node states. Ordinary closed-fibre shrinking is valid by II 4.1.1, so no prime-to-ell shrinking or dimension-inductive repair is used here. No unit/chapter route was changed.

Nothing remains unfinished at this one-level split: the two new nodes deliberately remain statement-only, as required. The worker has not written Lean, compiled, run Lake, changed the shared repository, or started agents.

## Searches and duplicate checks

The original item and its inherited Mathlib searches were retained. New msearch.py calls are logged verbatim in searches.jsonl and recorded in the appropriate node. For the item and both new nodes I read LeanFinder and LeanSearch hits, tried Loogle and source grep, and used a second semantic phrasing. The hits are henselian root lifting, scheme morphisms, or ordinary limit statements; none supplies the alteration covering certificate or its marked spreading. Loogle gives no hits for the alteration/Henselian-proper/etale-regular name patterns; grep gives none except unrelated calculus comments. No Mathlib leaf was justified.

I searched the whole DAG for uniformization, henselian regular-pair spreading, ordinary alteration approximation, III 3.1 and II 4.3.3, and opened the related nodes. I ran blueprint_refs.py ancestor for the item and whole-blueprint searches for uniformization, alteration, henselian, approximation, normal crossings and henselization. The blueprint has no node giving either new interface. The ancestor remains lem-per-artin-gabber-affine-curve; the place and complete via chain are recorded. Neither new lemma is a clause of the item: approximation starts with an arbitrary given completion cover and concludes only covering of close specializations, without regularity; spreading starts with a prescribed henselization cover and concludes its finite-stage realization. Completion, approximation-section existence, boundary regularity, closed-fibre shrinking, normalization, finiteness and global assembly remain in the item's argument.

## Not duplicates

lem-per-ordinary-alteration-cover-approximation vs lem-per-alteration-cover-approximation: the existing node assumes a prime invertible in A and an ell-prime alteration cover; the new node is III 3.1(ii), for an arbitrary ordinary cover with no prime. An ordinary cover need not satisfy the existing premise.

lem-per-ordinary-alteration-cover-approximation vs lem-per-finite-generic-dominant-parts: the latter establishes alteration objects and behavior of etale families once finite generic fibres are known; it does not preserve a covering certificate under close approximation.

lem-per-ordinary-alteration-cover-approximation vs lem-per-marked-finite-diagram-approximation: the existing node preserves regularity and SNC intersections near special fibres and imposes no covering conclusion. The new node preserves the cover and imposes no regularity hypothesis.

lem-per-ordinary-henselian-regular-pair-spreading vs lem-per-henselian-regular-pair-spreading: the existing node requires a prime invertible on T and a specified ell-prime cover. The new node spreads an ordinary cover without either restriction; a given ordinary cover is not automatically such an ell-prime cover.

lem-per-ordinary-henselian-regular-pair-spreading vs lem-per-ordinary-henselian-pointed-neighbourhood-limit: that node constructs the henselization as a pointed-etale limit only; it does not descend a prescribed covering or boundary diagram to a regular model.

lem-per-ordinary-henselian-regular-pair-spreading vs lem-per-ind-etale-regular-coordinate-locus: the existing statement concerns openness/reflection of given regular-coordinate loci and has no preservation of an ordinary alteration covering certificate.

lem-per-ordinary-henselian-regular-pair-spreading vs lem-per-ind-etale-alteration-object-degree-descent: the existing statement explicitly has no covering-family, regularity or boundary conclusion; it also assumes an invertible prime. Spreading needs all three conclusions for the prescribed data.

lem-per-ordinary-henselian-regular-pair-spreading vs lem-per-nisnevich-cover-limit-descent: the latter descends complete decomposition for an etale leg, not a regular marked ordinary alteration cover.

lem-per-ordinary-alteration-cover-approximation vs lem-per-uniformization-complete-local-descent: that node is the prime-to-ell global reduction; the new node is just the ordinary approximation of the covering certificate, without any uniformization conclusion.

lem-per-ordinary-henselian-regular-pair-spreading vs lem-per-uniformization-complete-local-descent: that node is the prime-to-ell global reduction; the new node only spreads an already prescribed ordinary cover from one henselization.

## Review by Q119

I checked this split against delivery-errors B--E with the node statements and source text open. The new nodes contain statements and no proof sketches, introduce their own schemes and congruence maps, cite definitions for every specialized notion, and retain the ancestor and unit. I checked that their conclusions are actually asserted by the ordinary alternatives of the source. III 3.1(ii) permits approximation of the finite covering certificate, including dominant reduced parts. II 4.3.3 and the first paragraph of III 6.2 permit spreading a specified family and boundary intersections through the henselization limit. This does not follow merely from the definition of a henselization, which is why the second new node is necessary.

Step 1 uses the preparation node's actual normal-completion and nowhere-density assertions, then completion-dimension equality. It applies the item's hypothesis only to a nonzero normal complete Noetherian local domain with dimension at most d. Marked-diagram approximation supplies a model and regular SNC neighborhoods; ordinary cover approximation applies to that very model and supplies the independent covering threshold. I did not take covering preservation from the marked-regularity node or vice versa.

Step 2 uses Noetherian finite type implies finite presentation to put the model into finitely many equations. Excellence explicitly includes the G-ring property, so the cited henselian-pair approximation theorem applies to the maximal-ideal henselian pair and gives simultaneous congruence for all model coordinates. Evaluating polynomials gives congruence for the whole algebra, as the new cover lemma requires. The marked approximation statement explicitly says the dominant union is open and closed in its regular neighborhood; restriction therefore gives a regular marked open O_i in the dominant part. No regularity of the entire specialized scheme is assumed.

Step 3 uses exactly the ordinary proper-refinement node's integral proper surjective certificate and its finite Zariski refinement; the cited proper definition supplies closedness of the image of the complement. I wrote the shrinking argument out: every point of the closed fibre lies in the union of the inverse-image opens; a closed subset of Spec B missing its closed point is empty. The topology's transitivity, quoted from def-weil-pbc-topos, then proves covering after shrinking. This is a routine argument from the cited certificate, not an uncited use of a prime-to-ell shrinking statement.

Step 4 uses finite-type-over-Noetherian to justify the Noetherian spaces being split and the finite-components node to justify finite connected decomposition. The two-sentence closed-union/complement argument proves these connected components open and closed. The connected regular integrality theorem has exactly these hypotheses and is the source of integrality, which is required by U. Restriction of the boundary is checked from its actual definition: an open restriction of an integral component is integral if nonempty, and every intersection and codimension is checked on the same local rings. The case with no components gives the empty boundary.

Step 5 first uses reducedness and quasi-excellent localization on an actual affine chart, so preparation is applied to a reduced quasi-excellent local ring, not an arbitrary local ring. It supplies finite normalization, henselian excellent domain factors, the dimension inequalities and nowhere-density on every factor. Finite-proper supplies the properness needed for a covering generator; finiteness is not silently treated as proper by definition. Composing the normalization, its finite open-and-closed factor cover and the regular families uses precisely topology transitivity and finite-type composition. Generic residue-field extensions compose as finite field extensions, so the composites remain alteration objects. The normalization is not required to be regular.

Step 6 uses the new prescribed-family spreading statement, including that the pointed etale neighborhood itself is an alteration object and that its entire specified cover is regular with the correct support. The chosen equal-residue-field point at every base point verifies the hypothesis of the existing completely-decomposed finite-subcover theorem. It does not use Zariski quasi-compactness to extract an etale subcover without a node. The resulting finite jointly-surjective etale family is a covering generator; topology transitivity and finite-type composition give a finite ordinary family over S. Taking connected integral components again uses Step 4, whose inputs remain valid.

Step 7 cites the local finite-Krull-dimension theorem: no Noetherian scheme is assumed globally finite-dimensional. Preparation and completion dimension bound each actual B_a and its completion at a given s, so the complete-local hypothesis in every finite dimension suffices. Finite extraction is independent of these varying bounds. The empty scheme uses the empty covering, d=0 still applies without an induction/base-case gap, fields have empty nowhere-dense boundary, and Z empty is permitted by the marked-diagram statement. I also tested the first new statement on the identity cover over a field or complete DVR, and the second on the identity family with no boundary and on a pointed etale model: no nonempty-fibre or positive-dimension assumption was inadvertently added.

Every cited node's statement was read; citations.json contains one verbatim statement quotation for each step-node pair (including the definitions used for the elementary parts of the argument). All steps are below 2000 characters; the explicit shrinking, polynomial evaluation, connected-decomposition and dimension-chain arguments hide no independent lemma. Generic off-unit algebra/topology tools are disclosed in split_report.tool_uses; no off-unit uniformization theorem replaces the unit route. The initial server review_split check passed. The required delivery dry run and push are performed after this report is written.

The first delivery dry run rejected grouped bracket citations in the spreading statement. I changed all new-node notion references to individual [node-id] citations and regenerated the verbatim citation manifest; the mathematical statements are unchanged.
