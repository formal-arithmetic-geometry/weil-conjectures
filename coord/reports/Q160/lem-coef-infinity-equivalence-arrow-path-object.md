# Worker report

## Files written

- dag/nodes/sec-six-functors/lem-coef-infinity-equivalence-arrow-path-object.json: statement item split into five proof steps; original statement and statement dependencies unchanged; no Mathlib match.
- citations.json: a verbatim statement quotation for every step/node pair. Model-node quotations include its complete statement, since the steps need several distinct clauses.
- searches.jsonl: five real msearch.py searches (LeanFinder twice, Loogle, Mathlib grep, LeanSearch); the item retains its inherited search records and appends these actual results.
- report.md: this report. write_split.py is the sandbox-local writing helper, not a delivery file.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searched the project source under /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint id and the notions marked internal Hom, equivalence arrows, and path objects. The matches are ordinary categorical structured-arrow equivalences and unrelated marked geometric points, not this construction. There is no completed declaration of this item to attach.

## WANTED

WANTED: Jacob Lurie, Higher Topos Theory, Section 3.1.3 opening internal-Hom formulas (printed p. 154), Proposition 3.1.4.1 and Corollary 3.1.4.3 (printed pp. 160-162), for lem-coef-infinity-equivalence-arrow-path-object. The PDF is not archived under literature/. I read these places online at https://www.math.ias.edu/~lurie/papers/HTT.pdf on 2026-10-17 without downloading a file. The proof is marked agent-written and explicitly derives the construction from the existing marked-model node.

## Corrections and source audit

The local shared snapshot did not yet contain the assigned node. I recovered its existing JSON from /home/ubuntu/weil-newtargets/dag/nodes/sec-six-functors/lem-coef-infinity-equivalence-arrow-path-object.json on the Weil server using a read-only cat over ssh, writing the copy only to this item's sandbox. Its status was unsplit, its proof empty, and its creation stamp belongs to ND's functor-pushout split. I preserved that stamp and the inherited blueprint ancestry. The delivery tool overlays against the current server-backed origin and preserves maintainer-owned metadata.

There is no statement dispute. In particular, the current statement asserts the endpoint model fibration and the natural marking; it does not assert that the identity-arrow map is a weak equivalence. Despite the historical id ending in path-object, the split proves exactly the current statement and needs no separate path-object weak-equivalence lemma.

The fixed chapter, the recorded sk-prop-sf-biduality-general unit, and the main-20261015 blueprint integral-adjoint statement and proof were read. This child realizes the technical coherent-diagram mapping foundation identified in its existing ancestry, not a replacement of a chapter or unit step. The model theorem is in the same recorded unit. The enhanced-diagram dependency is a definition, hence a notion dependency rather than a departure from the route. No off-unit theorem is used, and no unit record is changed.

The DAG and whole-blueprint searches for equivalence arrows, marked simplicial objects, internal Homs and pushout products located the existing lem-coef-marked-point-cartesian-model. Its statement already includes both the marked exponential adjunction and the cartesian pushout-product axiom. There is no reason to create either a general exponential-fibration node or a restatement of an item clause: the actual diagonal construction is short and is written in Step 3. Blueprint same_as is empty: no imported blueprint node states this technical assertion.

The fresh Mathlib searches returned unmarked Kan-Quillen horn/boundary declarations, basic quasicategory fillers, and abstract model path-object projections. I read InnerFibration.lean:55-103 and PathObject.lean:45-140. Those path-object projections require an already given good path object; they cannot construct or identify this marked exponent, and the Kan model is not the marked cartesian model. The second LeanFinder query specifically searched restriction of the marked internal Hom to the two interval vertices, again without a match. No recorded fresh search was invented or converted from an unavailable response.

## Review by Q160

I read HTT's actual internal-Hom formula on printed p. 154, its fibrant-object characterization in Proposition 3.1.4.1, and the cartesian pushout-product assertion in Corollary 3.1.4.3. These agree with the precise clauses used from the opened statement of lem-coef-marked-point-cartesian-model. I also opened and read def-cbc-enhanced-diagrams-cones for the equivalence-edge and full-subcategory conventions. No source in the prohibited SGA route is used.

Step 1 takes the marked Hom adjunction, flat and sharp markings, the product marking, and natural marking from the model node. It tests every marked edge in the product: the first coordinate must be degenerate, so the only nondegenerate conditions are the vertical equivalence edges at individual vertices. Conversely those conditions suffice. The definition node supplies precisely the description of a full subcategory by its vertices. The proof therefore identifies all simplices and all operators, not only objects; no pointwise-equivalence theorem is silently invoked.

Step 2 uses the same model node's cofibration criterion and adjunction. The interval boundary has two constant simplices in each degree. Its product with an arbitrary marked object consists of two marked copies of that object, which proves the exponential identification with the product target directly. This checks that the map whose lifting problem occurs in Step 3 is the actual endpoint map of the statement, with the correct markings.

Step 3 uses three theorem clauses actually stated by the model node: the cartesian pushout product is trivial when one cofibration is trivial; C-natural is fibrant; fibrations are characterized by lifting against trivial cofibrations. The boundary inclusion is a cofibration regardless of C. I wrote the entire transposed square with its pushout source and both restrictions; the resulting extension has exactly the prescribed endpoints and agrees with the given map on T. No equivalence-edge lifting theorem is assumed beyond the cited model result.

Step 4 uses the same three clauses, with the empty-to-interval cofibration. The pushout product is written explicitly as T times J to T' times J. This proves fibrancy for both interval markings and then applies the node's exact fibrant-object characterization. It proves W=V-natural instead of treating the marking as obvious. Using the flat interval in the same calculation confirms the ambient Fun(Delta^1,C) is itself a quasicategory. This is a short direct application of an existing axiom, not a hidden new lemma.

Step 5 uses the definition node's inverse-with-two-triangles criterion: applying a simplicial map to those witnesses preserves equivalences. Postcomposition and endpoint restriction then commute on each simplex. The model node explicitly provides its construction and fibrancy assertions in the input universe and under enlargement. I checked the empty input directly: every Delta^n times Delta^1 has a vertex, so there are no simplices of V when C is empty, and the endpoint map is the identity of the empty marked object. No nonemptiness premise or arbitrary vertex is introduced. The terminal category, discrete categories and the nerve of a category with noninvertible arrows give the expected tests: equivalence arrows only, while horizontal morphisms in V need not all be equivalences.

Against delivery-errors B-E: there are no new nodes, duplicate clauses, unsearched notions or statement-only proof sketches; all statement notions retain their existing definition/model dependencies. Every non-elementary assertion is in the cited model theorem's statement, and citations.json exposes those exact statements. All five steps have explicit booleans and source places, all proof dependencies are precisely the union of uses, the original statement is unchanged, and every step is shorter than 2,000 characters. The marked model theorem's existing statement is sufficient, so I corrected no other node and introduced no unnecessary dependency. The proof does not use its item or descendants; the server checks verify the resulting DAG.

## Not duplicates

No new node was created, so there are no new/existing pairs to distinguish.

## Unfinished work

None in the mathematical split. Validation and delivery use the required server tools; their final outcome is reported by the delivery command.
