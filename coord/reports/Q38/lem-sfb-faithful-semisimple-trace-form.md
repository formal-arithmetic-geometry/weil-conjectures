## Worker report

Item: lem-sfb-faithful-semisimple-trace-form. Group Q38. Stage 1 only, direct delivery, 2026-10-24.

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-faithful-semisimple-trace-form.json: split into four steps following Milne §22c, printed p.475 (PDF p.487). Mathematical hypotheses and conclusion unchanged; added explicit references to the existing finite-dimensional-space and ordinary-trace definitions.
- dag/nodes/sec-six-functors-basics/lem-sfb-cartan-trace-criterion-characteristic-zero.json: statement, not a Mathlib match; attached to an existing closed project theorem. No proof steps added to this child.
- citations.json: verbatim statement quotations for every step/use pair.
- report.md: this report. searches.jsonl was produced by msearch.py.

Attachments: LieSubalgebra.isSolvable_of_trace_mul_eq_zero belongs to the new node lem-sfb-cartan-trace-criterion-characteristic-zero, WeilConjectures/Mathlib/Algebra/Lie/CartanCriterion.lean:48–70, variables at 41–42. This declaration is also already attached to the narrower existing node lem-wf-cartan-trace-criterion. Its generality exceeds that node's written statement; the existing node was not edited.

WANTED: none required for this split. Milne states the arbitrary-field trace-form assertion and invokes Cartan's criterion; the criterion's full general-field statement and proof are available in the project source. Humphreys 1972 §4.2 is Milne's bibliographic reference, not an unread source claimed to have been consulted.

No prior attempt, repair order, or report existed in this sandbox. The item is live-unsplit. No exact project declaration was found for the item, by its blueprint tag or by Lie trace-form/semisimple/Cartan searches. The project Cartan criterion is a prerequisite, not an attachment of the item itself. No statement dispute or departure from the unit route was found. Nothing remains unfinished in the requested one-level split.

## New nodes

lem-sfb-cartan-trace-criterion-characteristic-zero is a general linear Cartan solvability criterion. Its hypotheses do not assume semisimplicity or faithfulness; its conclusion is solvability, not nondegeneracy. Thus it is neither a clause of the item nor a relocation of the whole proof. It already has a closed project declaration and is not being split further. Status remains unsplit with the existing closed declaration recorded in lean_audit, as the worker brief requires for a non-Mathlib new statement with an attachment.

Its statement introduces F, M, the bracket-closed linear subspace A, the bracket span, the trace vanishing condition and the terminating derived series. The definition nodes cited actually define those notions. There is no proof sketch in the statement. Milne's standing assumptions at the beginning of §22c are a characteristic-zero field and finite-dimensional Lie algebras and representations. The attached theorem has precisely Field, CharZero and FiniteDimensional M; it imposes no IsAlgClosed, nonzero-space, irreducibility, or Killing-form hypothesis.

## Not duplicates

lem-sfb-cartan-trace-criterion-characteristic-zero vs lem-wf-cartan-trace-criterion: the existing written statement fixes the coefficient field to Qlbar. The new statement permits an arbitrary characteristic-zero field, as the item requires. Although the existing attached Lean theorem already has the generality, using the narrower DAG statement for arbitrary F would violate C4.

lem-sfb-cartan-trace-criterion-characteristic-zero vs sk-lem-walg-trace-criterion: this newly imported sketch leaves the scalar field and finite-dimensionality implicit; its chapter explicitly works over an algebraically closed characteristic-zero field. The new self-contained statement covers arbitrary F and records the already proved general-field declaration. Neither existing record is changed. There is no Stacks tag shared by these nodes: this is a Lie-theory criterion, sourced to Milne's invocation and the read project theorem, not a Stacks lemma.

Whole-DAG statement/title searches for Cartan, trace forms, solvable ideals and cyclicity, and searches for the actual declaration, found the two records above, Killing-form nodes and the existing cyclic-trace leaf. Whole-blueprint searches using tools/blueprint_refs.py for Cartan, trace criterion and trace form found no other general-field criterion or arbitrary faithful trace-form theorem. I read the current latest blueprint's sk-lem-walg-trace-criterion and its chapter convention. The new node and item have same_as = []. The existing item's inherited blueprint ancestor is null; blueprint_refs.py ancestor confirms None. The new node preserves that ancestor, prepends the item to the via chain, and specifies the Cartan step in from.place.

## Mathlib searches

All new search entries were actually run using msearch.py and are in searches.jsonl. The item has six additional searches: LeanFinder in two phrasings, Loogle for traceForm/Nondegenerate, LeanSearch for the trace radical, and two greps of Algebra/Lie (including CartanCriterion). The child has LeanFinder in two phrasings, Loogle for isSolvable/trace, LeanSearch for the linear Cartan criterion, and a grep for trace solvability statements. All services answered successfully; none is recorded as unavailable.

I read Mathlib/Algebra/Lie/CartanCriterion.lean, TraceForm.lean's symmetry statement, and Weights/Killing.lean's Cartan restriction statement. Mathlib's traceForm_cartan_nondegenerate restricts the adjoint representation to a Cartan subalgebra, and traceForm_nondegenerate concerns field extensions. Neither is this item's arbitrary representation. CartanCriterion supplies nilpotence of a derived action for a zero trace form and Killing-form solvability criteria, not the exact linear-subalgebra criterion. The latter is supplied by the project theorem. There are zero new Mathlib leaves.

## Review by Q38

I read Milne, Algebraic Groups (2017), §22c, printed p.475, including the standing characteristic-zero and finite-dimensional assumptions and the paragraph identifying the trace-form kernel as a solvable ideal. For the child I read the full project declaration, its variables and proof at lines 41–70, and the existing closed audit in lem-wf-cartan-trace-criterion. This checks the general field rather than silently applying the Qlbar-only DAG statement. The proof contains no sorry, and the existing audit reports no open dependencies. No compiler or Lake tool was used.

Step 1 uses def-weil-endomorphism-trace for the diagonal sum, which gives linearity by adding and scaling diagonal entries, and lem-pc-finite-dimensional-trace-cyclic for the two compositions on the same finite-dimensional M. Their statements give exactly these facts. Composition bilinearity is elementary.

Step 2 uses def-wf-lie-algebra for bracket preservation and the definition of ideal, and the cyclic-trace leaf for Tr(ZXY)=Tr(XYZ). The full commutator expansion is written in the step, with the sign checked: B([z,x],y)=B(x,[y,z]). Since x annihilates every second argument, [z,x] lies in R. There is no assertion that the kernel is an ideal without its calculation.

Step 3 uses the new criterion exactly on A=rho(R), a bracket-closed subspace of End_F(M). The field F has characteristic zero and M is finite-dimensional, as required. The trace vanishes on A times A because each first preimage lies in R; since [A,A] is a subspace of A, the criterion's weaker vanishing hypothesis follows. No semisimplicity of the representation or algebraic closure of F is used. The Lie definition node supplies bracket closure, not solvability.

Step 4 uses the derived-sequence definition in def-wf-lie-algebra and the no-nonzero-solvable-ideal definition in def-wf-semisimple-lie-algebra. The elementary induction rho(D^j R)=D^j A is explicit at its base and successor; rho is injective, so termination in A implies termination in R. Only then is semisimplicity used to kill the ideal. The citation is its statement, not a theorem about the radical hidden in a definition's proof.

I checked B–E against both node files. The only substantial input newly exposed is the independent Cartan criterion; elementary symmetry, the ideal calculation and transport of bracket spans stay in the item's steps. Every non-elementary fact has a node citation, and every citation has a verbatim quotation in citations.json. The longest step has 525 characters, so no long step hides another lemma. The new node has no proof or proof dependencies and all mathematical notation is single-escaped TeX in JSON.

Small cases: L=0 gives a zero-dimensional radical and the asserted implication holds for any M, including M=0. If M=0, injectivity forces L=0. The Cartan child includes A=0 and M=0; for a one-dimensional abelian A its derived algebra vanishes and its conclusion is correctly solvability. Trace-zero strictly upper triangular matrices satisfy the criterion and are solvable. A nonfaithful zero representation of sl_2 would have a degenerate trace form, confirming why the item's injectivity is used in step 4; no such case has been discarded. Non-algebraically-closed fields such as Q are explicitly allowed by the attached theorem. I added the general-field child instead of misusing either narrower blueprint statement; no mathematical change to the item was necessary. No SGA source, Lean edit, build, or repository write was used.
