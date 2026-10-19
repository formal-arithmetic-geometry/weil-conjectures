# Stage-1 report: lem-exc-closed-lift-filtered

## Files written

- dag/nodes/sec-smooth-purity/lem-exc-closed-lift-filtered.json: existing statement node, split into six steps; no complete Mathlib match found.
- citations.json: one verbatim statement quotation for every node cited in every step.
- report.md and the search command's searches.jsonl: review and actual search records.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: this item is auxiliary, not the unit's statement node.

## Attachments

None. Searched WeilConjectures in /home/ubuntu/weil-src-slopmaster2 for the item id and the closed-lift notion. Algebra.ClosedLift.isFiltered_index, WeilConjectures/RingTheory/ProEtale/ClosedLift.lean:142, states the desired filteredness for an arbitrary commutative A-algebra, but its body at line 143 is sorry. It is not an attachment. Read the indexing objects and compatible morphisms in lines 57-88 and the docstring explaining the small model. The Lean model uses ideals of relations rather than explicit finite lists; the DAG definition uses explicit finite presentations. This affects presentation data, not the compatible algebra maps used here. No proof or attachment is claimed from upstream master.

## WANTED

None. All sources needed here are available locally.

## Corrections and scope

The statement remains unchanged and is true under the hypotheses in def-exc-ind-etale-closed-lift. The original proof pointed to lem-weil-pbc-ind-etale-stability for finite etale base change/composition and an open-and-closed finite diagonal. Its statement does not assert these facts, so that citation was removed. It would be a C4 error to use its proof instead of its statement.

The corrected proof retains the blueprint's common tensor successor and quotient by differences, which is the pullback of the diagonal. The diagonal is etale by the existing cancellation lemma applied to the two etale A-schemes. Its pullback is etale by base change, and the successor is etale over A by composition. Open-and-closedness and an idempotent description are stronger facts not needed in this proof. Explicit finite presentations replace any implicit assumption that an etale scheme map automatically supplies the precise presentation data required in the small model.

The chapter and unit were read: sec-smooth-purity and sk-prop-sf-open-closed-triangle. This is an auxiliary algebraic construction inside the closed-support argument, with no replacement of the unit's open-closed stalk proof. The off-unit etale stability/cancellation and affine fibre-product statements are generic tools; their uses are requested here as generic tools for maintainer review; split_report.tool_uses is empty, since accepted tool uses are recorded by the maintainer. The tensor universal-property node is also a generic algebraic tool (already a Mathlib leaf). Definitions of finite presentation and filtered categories supply notions.

## Search and duplicate review

Ran the six recorded msearch.py queries and read their hits. LeanFinder's first phrasing finds finite presentation/descent, not the complete comma category. The second phrasing finds etale composition and the category of etale schemes, also not the item. Loogle finds no joint Algebra.Etale/IsFiltered result. The first grep finds Mathlib/AlgebraicGeometry/Sites/EtalePoint.lean:56; read that instance in context: it concerns etale neighborhoods of a morphism from the spectrum of a separably closed field and has a different index category. It does not directly specialize to the finite-presentation algebra model with arbitrary target C. The second grep finds no filteredness declaration in RingTheory/Etale. LeanSearch returned Internal Server Error and is recorded as unavailable.

Searched the complete DAG and blueprint with blueprint_refs.py search 'closed-lift' and 'etale diagonal', and searched the DAG statements for tensor/fibre-product and pushout assertions. The existing tensor pushout, affine spectrum fibre-product, etale stability and cancellation nodes suffice. The other closed-lift blueprint nodes concern reduction, units and adjunction, not filteredness. Thus same_as is empty. No new nodes were proposed, so none can be elementary, duplicates, restatements of a clause, or missed Mathlib leaves.

## Not duplicates

No new nodes.

## Review by NV

I read both paragraphs of the master blueprint item, its neighboring closed-lift definition, the complete cited statements, and the relevant local Stacks sources. Specifically: algebra.tex Definition 00F3 (definition-finite-type) for finite presentations; schemes.tex Lemma 01I4 (lemma-fibre-product-affine-schemes), including its tensor universal-property proof; morphisms.tex Lemmas 02GP (lemma-open-immersion-etale), 02GO (lemma-base-change-etale), 02GN (lemma-composition-etale), 02GW (lemma-etale-permanence); and categories.tex Definition 002V (definition-directed). There are no new-node sources to review. I also examined the idempotent-section splitting statement and its sources 00U7/00U8 and 09XI while diagnosing the original citation, but the final proof needs none of these extra results.

Step 1 uses def-exc-ind-etale-closed-lift for the objects, def-weil-pbc-finitely-presented-algebra for the zero-generator presentation, and clause (1) of lem-weil-pbc-etale-composition-cancellation for the identity open immersion. This proves nonemptiness rather than assuming the target algebra has a point or is nonzero.

Step 2 uses the affine fibre-product statement, which explicitly identifies both projections, and clause (1) of the etale base-change statement, followed by clause (2) of the composition statement. All bases are spectra of arbitrary commutative rings, so no noetherian, finite-field or finite-type hypothesis is imported. The tensor universal-property statement gives exactly the product map q(b)q'(b') and both compatible inclusions. The finite-presentation definition and the explicit concatenation of variables and relations prove finite presentation over A. The presentation isomorphism transports every arrow to an actual object of the small model, whose definition retains all compatible maps.

Step 3 applies step 2 to B with itself, so both source and target of Spec(mu) are etale over Spec(A). Clause (3) of the composition-cancellation node states exactly that an arbitrary morphism between such schemes over the base is etale. The tensor node defines mu and h, with their actual factor formulas; compatibility with A is built into these algebra maps. This proves the diagonal property needed here, without citing a diagonal property absent from the ind-etale-stability statement.

Step 4 uses only the finite generators in the presentation and the explicit tensor universal property. The calculation on b tensor 1 and 1 tensor b forces v=uf=ug, and conversely this identity gives the balancing equation. It proves the quotient/pushout identification, not merely a set-theoretic image assertion. Agreement on the finite generators implies agreement on all polynomials and their quotient, so the finitely generated ideal equals the ideal of all differences. This is an elementary calculation from the quoted statements, not a new theorem node.

Step 5 uses the same affine fibre-product assertion over the ring T_0, so the correct base-changed map is Spec(mu), not Spec(B)->Spec(A). The base-change and composition clauses have exactly these etale hypotheses. A finite presentation of B' with the finitely many polynomial representatives H_i adjoined proves finite presentation of Q; no finiteness of an arbitrary ideal is assumed. The equality q'f=q'g follows from the definition of parallel arrows in the indexing category and proves that q' kills J, giving the required descended map and arrow. The quotient equalizes both arrows even when it is the zero ring.

Step 6 uses the explicit three filteredness conditions stated in def-weil-pbc-category-colimit and the morphism convention of def-exc-ind-etale-closed-lift. Each condition has already been proved. No existence, smallness or finiteness condition is taken from a proof rather than a cited statement. The index category is small by its explicit presentation model; the argument uses only finitely many generators at each construction and does not need a colimit or a large index category.

I tested A=0, I=A and C=0 (allowed unital zero rings), B=A, the case f=g (J=0), and zero generators or zero relations. The identity object, tensor presentation, finite-difference quotient and compatibility equations remain valid in all cases. Neither ind-etaleness of C over A/I nor properties of I are used; the proof works for arbitrary commutative A-algebras C and therefore proves the stated special case without dropping its hypotheses. No statement dispute arises.

For delivery-errors B-E, the packet has no new-node statements or proofs to misclassify; all TeX is singly escaped in the JSON values; every non-elementary step cites the actual stability, cancellation, tensor or affine-product statement it uses; the elementary quotient calculation is written out. The proof is not moved into a new node and follows the same tensor/diagonal route as the blueprint. I checked the dependency closure of every proposed citation: none reaches this item, so the added citations introduce no cycle. citations.json copies the complete statements verbatim to make every use independently checkable.

## Unfinished work

None in this one-level split. The existing cited nodes retain their own states. No Lean was written, no compiler or Lake was run, and no delivery was pushed. The fresh second reader should independently verify the six steps and the sources before delivering.

## Second reading by NV

- Item statement: compared verbatim with master blueprint lem-exc-closed-lift-filtered and the hypotheses of def-exc-ind-etale-closed-lift; agrees, with no hypothesis change. Read both blueprint proof paragraphs and the chapter/unit route.
- Step 1: checked the indexing definition, finite-presentation definition (00F3, definition-finite-type), and cancellation node clause (1) against 02GP, lemma-open-immersion-etale; valid identity object, now also explicitly represented by the zero-variable polynomial quotient.
- Step 2: checked tensor universal-property clauses (1)-(3), affine-product statement against 01I4, lemma-fibre-product-affine-schemes, base-change clause (1) against 02GO, lemma-base-change-etale, and composition clause (2) against 02GN, lemma-composition-etale; all apply over arbitrary A. Concatenated generators/relations give the required finite presentation. Replaced “transport” with explicit inverse-isomorphism formulas and both compatibility equations.
- Step 3: checked the tensor node supplies both mu and h, and cancellation clause (3) against 02GW, lemma-etale-permanence; both source and target of Spec(mu) are etale over Spec(A), and mu is an A-map. Thus the diagonal is etale with precisely the hypotheses available.
- Step 4: checked the finite-presentation and tensor statements directly; the elementary calculation evaluates the balancing identity on b tensor 1 and 1 tensor b, obtains v=uf=ug, and characterizes quotient maps. Agreement on the finite algebra generators extends to polynomials, so the finite differences generate all differences. The inverse universal maps are over B-prime, as required for the next base change. Valid; no additional lemma or node needed.
- Step 5: checked 01I4 and the cited base-change/composition clauses with base Spec(T_0), not Spec(A). The finite H_i exist from the presentation of B-prime; adjoining them presents Q. The compatibility q-prime f=q-prime g gives the descended map. Replaced implicit presentation transport by a=e^{-1} pi and verified both its cocone compatibility and af=ag.
- Step 6: checked the three conditions in def-weil-pbc-category-colimit against 002V, definition-directed (the index-category version erases M from condition (3)); steps 1, 2 and 5 give exactly those conditions in the small model. Valid elementary conclusion.
- New nodes: none. B1-B7 and the new-node elementary/duplicate/restatement/Mathlib-leaf tests have no proposed node to reject. Independently searched the complete blueprint for closed-lift; the other hits state definitions, adjunction, reduction or units, not filteredness.

Independently ran msearch.py with the scheme/opposite-category phrasing “The opposite category of affine etale schemes over S equipped with a map from a fixed affine S scheme is filtered”, and grep “IsCofiltered|IsFiltered” in AlgebraicGeometry/Sites. Read the returned types and EtalePoint.lean:29-57: the concrete cofilteredness instance there assumes a separably closed field point and concerns all etale schemes; it is not a one-line specialization to this explicit finite-presentation affine model with arbitrary C. The semantic hits supply etale categories, pullbacks or cancellation, not this indexing-category statement. Both searches are recorded as returned in searches.jsonl. Read ClosedLift.lean:57-88,140-143 in the read-only slopmaster2 source: its filteredness instance is sorry, so it is not a finished proof or attachment.

Edge cases checked independently: A=0 forces the zero algebra and still supplies the identity object; for A a field and C=0 the zero quotient remains permitted; I=A forces C=0; f=g gives J=0; n=0 gives no differences since A-maps out of A coincide. Zero variables/relations and empty spectra do not invalidate any presentation or etale base change. No statement dispute was found. Verified all 21 verbatim citation entries against the dependency files and checked that their dependency closure has no return path to the item.

Changes: made the small-model identity, common-successor and equalizer maps explicit instead of saying “transport”; adjusted the final reference to those maps; corrected the first report's assertion that tool uses were already registered (the list is empty, and registration belongs to the maintainer). The existing report and Review by NV remain. No new node, statement change, Lean edit, compilation or live-project write was made by this reading.
