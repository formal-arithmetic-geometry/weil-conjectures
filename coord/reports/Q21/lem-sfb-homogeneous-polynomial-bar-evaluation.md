# Stage-1 worker report

Group Q21; item lem-sfb-homogeneous-polynomial-bar-evaluation; original split 2026-10-22; promotion-return repair 2026-10-23.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-homogeneous-polynomial-bar-evaluation.json — statement node split in eight steps; no exact Mathlib match. The statement and its statement dependencies are unchanged.
- citations.json — verbatim statement passages for every node used by every proof step.
- searches.jsonl — actual msearch.py results, retained with the earlier searches in the copied item's mathlib_searches.
- report.md — this report. write_split.py is sandbox-local preparation only.

Zero new nodes and zero Mathlib leaves. No unit record is changed: this item is a descendant of the open-image input, not the unit's statement node.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, homogeneous/polynomial/bar terminology and related evaluation declarations. Project polynomial and ordinary group-cohomology declarations do not state this internal condensed comparison, with its slice naturality and all continuous coefficients.

## Wanted literature

WANTED: an exact written reference for homogeneous polynomial evaluation into the internal condensed bar complex with all continuous noncomplete algebraic-closure coefficients, for lem-sfb-homogeneous-polynomial-bar-evaluation. The supplied blueprint paragraph (3) delegates the open-image input and contains no proof of this polynomial sub-obligation. The proof is therefore explicitly marked agent-written. No unavailable theorem from that wanted reference is used as a premise.

## Corrections and source observations

The source is literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3). I read that paragraph and the current chapter and unit. The historical dag/units record still reproduces the older snapshot; the current blueprint _section.md and current paragraph (3) give the operative open-image place. This split stays within that place. There is no statement dispute and no change of coefficient category or topology.

The imported item has no proof. I supplied the evaluation construction and all identities rather than replacing it by another node with the same conclusion. The polynomial invariant-coordinate identification is already stated by lem-sfb-homogeneous-polynomial-invariant-coordinates, so I cited it instead of duplicating it. I did not use the finite-complete-field-only acyclicity theorem lem-sfb-normed-scalar-profinite-hom-acyclic for Omega.

The inherited blueprint.from.node was null. The read-only ancestor command also reports None because the created.item chain terminates at the historical module name Sheaf.SixFunctors.CtfStabilityDirectImages. Reading the existing chain reaches lem-sfb-admissible-direct-image, whose blueprint.from.node is det-thm-sf-ctf-stability-direct-images, an existing imported blueprint node. I filled this item's from.node with that documented ancestor and kept its via list. No tool or other node was edited.

Mathlib searches with both phrasings found ordinary polynomial evaluation, MvPolynomial.continuous_eval and abstract group cochain declarations. I read Algebra/MvPolynomial/Eval.lean and Topology/Algebra/MvPolynomial.lean. The former provides finite-sum polynomial evaluation and the latter continuity in variable assignments. They do not provide the internal map out of a sheaf coproduct with the specified equivariance and prefix normalization. LeanFinder additionally returned ContinuousCohomology declarations in Algebra/Category/ContinuousCohomology/Basic, but that file is absent in the pinned local Mathlib. No such hit is claimed as a local declaration or Mathlib leaf. The broad second grep also returned unrelated evaluation tactics; these were not counted as evidence for a match.

## What remains unfinished

Nothing in the assigned split. The existing invariant-coordinate node remains an independently queued obligation; this delivery neither claims to prove it nor modifies it. The wanted reference concerns provenance, and the proof here spells out the elementary evaluation argument without relying on an unseen reference.

## Not duplicates

No new nodes. The whole-DAG searches for homogeneous polynomial/functions, prefix sums and continuous polynomial evaluation, and whole-blueprint searches for homogeneous polynomial, prefix and polynomial, found no blueprint statement identical to this item. The existing polynomial invariant-coordinate node supplies precisely the invariant identification used in step 5; the topological homogeneous-coordinate nodes concern ordinary vector spaces, and the internal bar-normalization node additionally fixes injective resolutions and derived comparison data. Neither is a reason to create a second copy or to claim an exact Mathlib attachment.

## Review by Q21

I checked this proof against delivery-errors B through E with the supplied current blueprint paragraph and each cited statement open. There are no new statements to test, no new source tags to distinguish and no new statement-only nodes hiding proof text. The eight steps carry the evaluation argument itself, so there is no transfer of the item's conclusion to a new lemma. Every step is under 2000 characters. I judged each elementary step from the explicit substitution, finite product, universal-property or face calculation it contains; the invariant-polynomial theorem is the one non-elementary input and is marked accordingly.

Step 1 uses the polynomial ring node's actual universal property, the bar-data node's natural-family description of internal functions and its bar faces, and the homogeneous-function node's actual action formula. On a summand a substitution has finite support, so its extension out of the coproduct is legitimate. The double-deletion cancellation supplies the complex identity; no sheaf exactness or acyclicity is inferred from these definitions.

Step 2 uses the continuous-map condensed-ring node for the ring of all continuous functions and pointwise restriction, and the bar-data node for the precise slice-family interpretation. I checked continuity using the restricted norm on Z_ell inside F and finite products, and checked naturality by composing every input with a profinite map. Defining the map on summands and extending by the coproduct avoids assuming that every section globally has a fixed finite polynomial support. There is no infinite series or passage to the completion of Omega.

Step 3 uses the polynomial universal property to compare the two evaluation homomorphisms, the homogeneous-function action formula for the translation sign, and the action-module definition to interpret equivariance after every base change. The sign is y-g on both sides and the scalar action is trivial, exactly the hypotheses in force. Step 4 again uses polynomial evaluation on variables and the natural-family description. It compares each omitted coordinate with that same face, retains every alternating sign and sends the constant augmentation to constants.

Step 5 uses the statement, not the proof, of lem-sfb-homogeneous-polynomial-invariant-coordinates: it explicitly asserts the cochain isomorphism by consecutive differences and its prefix-sum inverse, including locally finite sheaf sections. Its ell, E, Omega, F, rank, universe and all-base-change fixed-section hypotheses are identical to the item. The action-module node's fully fixed section definition is the same convention. I did not borrow higher derived-invariant acyclicity from this node, which does not assert it.

Step 6 uses only the bar-data node's internal natural families, the homogeneous-function translation action, and the fully fixed condition of the action-module node. The displayed inverse is defined on every profinite slice; the translating h_0 is itself a continuous section on that slice, so fixedness really applies. Both composites are written as evaluations on reconstructed tuples. Step 7 checks the first face by translating by g_1, the middle faces by merging adjacent differences, and the last by dropping the last input. Its two cited definitions give exactly those faces and the permitted invariant translation. Thus it proves the cochain identity rather than merely asserting that a coordinate change transports it.

Step 8 uses the same existing polynomial-coordinate statement and bar-data definition to compute the composite on each monomial. The telescoping identity is displayed. I checked n=0, r=0, n=1 with r=1 (the interior term evaluates p(g_1+g_2)), and arbitrary nonconstant c in C(S,F): restriction pulls c back and every translation fixes its S-coordinate. For r=0 the alternating differential is 0 in even degree and the identity in odd degree; it is not mistakenly treated as the normalized complex concentrated in degree zero. The empty profinite parameter imposes no exceptional choice. These checks retain every clause and every hypothesis of the imported statement.

Finally I generated citations.json from the actual statements just read, and checked that every quote is a substantive verbatim substring for the corresponding step. Proof dependencies are exactly the union of uses; there is no citation of a source document in place of a node and no invocation of SGA, completeness, injectivity, or a derived comparison theorem. Existing input dependencies introduce no path back to this item.


## Promotion-return repair — 2026-10-23

The return says that the reader approved the split but landing did not promote the side-project completion into the live DAG. I retained the delivered proof, citation passages, report and actual search log. The retained receipt identifies the previous delivery as 5dbd4fd6aad; the retained node before this repair has SHA256 05ca7afc9ecb955f8d7b771f0a2ea4775f603ac3b5ccb0a9dd374824e8fbe8de. Against the current shared DAG, the item's statement, source, statement dependencies, title, chapter and unit still agree. Its current proof is empty and its status is unsplit, so this is still an actual split to promote, rather than a replacement of an already reviewed live proof. The required initial dry run rebuilt the retained split over current origin/sheaf-dag and passed at e0afde9af04 before any repair edits.

I re-read every current cited statement, including all statement-only inputs: def-sfb-continuous-map-condensed-ring, def-sfb-ladic-lattice, sk-def-sfb-module-objects, def-sfb-condensed-action-module, def-weil-size-convention, def-weil-pbc-mv-polynomial-ring, def-sfb-condensed-homogeneous-functions, def-sfb-condensed-equivariant-bar-data, and lem-sfb-homogeneous-polynomial-invariant-coordinates. All 19 retained citation passages are still verbatim passages of these current statements, and the step-by-step substantive checks in Review by Q21 above still hold. In particular the current bar-data statement supplies natural families on every slice, the homogeneous-functions statement supplies the inverse-translation action, and the invariant-coordinate theorem supplies exactly the cochain isomorphism used in steps 5 and 8, with the same all-continuous coefficients and the same fixedness after every base change. No proof of an input is used in place of its statement. Its unsplit status remains a separate obligation, not a claim of completion in this delivery.

I also re-read the current chapter, unit, and operative blueprint paragraph (3), and repeated the project-source attachment search; no exact completed project declaration was found. The original Mathlib search questions and the mathematical statement have not changed, so I read and reused the recorded results instead of rerunning them. No new nodes are introduced. The split_report now records the current repair date and this revalidation. No mathematical alteration to the accepted eight-step proof is needed: finite monomial substitution, the pairwise deletion cancellation, the slice-wise inverse using successive differences, and the face-by-face prefix calculation remain valid. Rechecking n=0 and r=0 gives the same augmentations and alternating unnormalized differential, and no completeness assumption has entered.

This repair changes the report and split_report and is packaged anew by deliver.py over the fetched current meeting-point branch, which retains its maintainer-owned fields. It does not attempt to edit the live DAG, promote a side completion directly, or bypass the maintainer's independent review. The final dry run and push follow this repair.
