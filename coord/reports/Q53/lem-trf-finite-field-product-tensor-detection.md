# Stage-1 report: lem-trf-finite-field-product-tensor-detection

## Files written

- dag/nodes/sec-trace-formula/lem-trf-finite-field-product-tensor-detection.json: statement, split; no exact whole-item Mathlib match. Statement unchanged; all inherited searches, source and provenance retained, and actual Q53 searches appended.
- citations.json: every proof-step citation, with verbatim statement quotes.
- report.md: this report. searches.jsonl is the search command's actual log.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag and id, tensor/product/injectivity terminology, and read the nearby FieldTheory tensor declarations. No project declaration gives all clauses. In particular, Mathlib declarations and project declarations with different hypotheses are not attachments.

## WANTED

None. The source used is present locally.

## Findings and proof

The live item is unsplit, there is no sandbox predecessor, and no released repair note was found. No mathematical statement error was found. The source Stacks algebra.tex, Tag 034N (lemma-geometrically-reduced-any-reduced-base-change), lines 10128-10151, compresses the finite-product passage into its final two sentences. This split supplies those calculations rather than citing them as an unexplained standard fact.

1. Define coordinate projections p_i and linear zero-insertions s_i. The tensor universal property defines Phi and the finite sum Psi. The identities p_j s_i = delta_ij and sum_i s_i p_i = id show both inverse identities on pure tensors and hence everywhere.
2. Calculate multiplication and the unit on pure tensors to upgrade Phi to an algebra isomorphism and show that j tensor 1 is a unital algebra map. The insertions s_i were deliberately used only as linear maps; they are not unital algebra maps.
3. Use existing field-flatness and tensor-exactness leaves on the module sequence 0 -> B -> P -> P/j(B). Compose the resulting injection with Phi to obtain precisely Theta, by its pure-tensor formula.
4. The existing tensor symmetry exchanges K_i tensor A and A tensor K_i. Verify its multiplicativity explicitly, then a nilpotent maps to zero in every reduced coordinate. Theta's injectivity gives zero in the source.

The item has four proof steps of 886, 681, 515 and 766 characters. None hides a long-step sublemma. The finite-sum inverse, multiplication check and nilpotent check are short computations from definitions and cited statements, so creating nodes for these would duplicate clauses or create elementary nodes (D1/D2 and the elementary-node prohibition). No new node is needed for the Mathlib piRight result: the proof writes the inverse calculation itself.

## Searches and not duplicates

DAG searches included the id, rTensor/lTensor preservation names, TensorProduct.piRight/piLeft, finite products of fields and tensor injectivity; blueprint_refs.py ancestor returned lem-trf-local-term-locality, and blueprint searches for finite products of fields, tensor injective, piRight and tensor products commute found no same-statement blueprint node. The broad tensor/product searches found ingredients but no existing statement of this whole item. The existing lem-trf-flat-tensor-preserves-injection is reusable but left-oriented; the stronger two-orientation leaf lem-weil-pbc-flat-tensor-exact is used directly. The existing lem-trf-finite-presentation-tensor-products concerns arbitrary products with a finitely presented tensor factor, a hypothesis absent here; it cannot be applied to arbitrary A. lem-pc-ring-extension-finite-support-product concerns sheaves and a functor with prescribed object function, not the present ring calculation. No duplicate new-node pairs exist because no nodes were created.

All Mathlib queries for this attempt ran through the required msearch.py and are recorded exactly in searches.jsonl and the item's appended mathlib_searches. The first interrupted tool session finished its four searches; its log was read before continuing, and those searches were not rerun. A second phrasing also ran. Read the actual candidate statements in GeometricallyReduced.lean:49-102 and Flat/Basic.lean:642-660: geometric reducedness and finitely-generated-subalgebra criteria do not state this item. Algebra.TensorProduct.piRight, TensorProduct/Pi.lean:55 (formula at 59), covers only the product isomorphism clause after swapping factors. Thus the whole item is not a one-line specialization of a hit. No service failure was treated as absence.

## Review by Q53

I read the chapter sec-trace-formula and unit sk-i-curve-zero, the current blueprint locality statement and proof, and Tag 034N in the local Stacks algebra.tex with its tag-to-label entry. This is the existing separable-constants algebra ingredient beneath that ancestor, not a replacement of the unit's contracting-correspondence route. The chapter, unit, target statements and repository were not edited. There is no SGA source in this delivery.

For step 1, I read def-weil-pbc-module-tensor-product in full: its statement actually supplies the bilinear universal property, generation by pure tensors and the maps f tensor id. That supports construction of both maps and extension of the two explicit inverse identities, rather than assuming that a product isomorphism follows just from a definition. For step 2 the same cited generation statement supports extending the displayed two-pure-tensor multiplication calculation by distributivity to finite sums; the unit is checked directly. No flatness or finite-dimensionality is being smuggled into those steps.

For step 3, I read lem-weil-pbc-module-over-field-flat: it states that every k-module is flat, including A of arbitrary dimension. I read lem-weil-pbc-flat-tensor-exact: its final clause explicitly preserves the leading zero and thus injectivity for tensoring on the right. The exact sequence uses the linear image j(B), not a ring ideal. Its hypotheses are satisfied since k is a field, j is k-linear and injective, and A is a k-module. These are Mathlib leaves, so their different unit is allowed as a tool without a route change.

For step 4, I read lem-weil-pbc-module-tensor-comm: it supplies a linear isomorphism with exactly the swap formula, but does not itself assert multiplicativity. The step therefore proves that property on pure tensors before mapping powers. It uses reducedness of A tensor K_i in precisely the orientation given by the hypothesis, then injectivity of each swap, equality of product coordinates, and the already proved injectivity of Theta. The citation file quotes each cited statement verbatim; no proof of a cited node is used instead of its statement (C3/C4). The algebra-map facts and finite product reducedness are proved as the elementary calculations, not uncited non-elementary facts (C1/C2).

I checked the small cases I empty (P=0 and injectivity forces B=0), I a singleton, A=0, B=0 where admissible, and two coordinates with different fields. The finite sum gives the zero inverse for the empty product, while 1=0 in that product, so the unital assertion is valid. For a nilpotent z the same exponent works in every coordinate; no inference that an arbitrary product of nilpotents is nilpotent is needed. Fields K_i need neither separability nor finite degree; no such hypothesis enters the argument. B and A need no finite generation. There was no correction of the statement, and no new statement requiring an independent small-case test (B1-B9, E1-E6).

## Unfinished work

None for this one-level stage-1 split. No Lean files were written and no compiler, Lake or build was run. The dry run and final delivery are the required server checks and push, performed by the supplied tool only.
