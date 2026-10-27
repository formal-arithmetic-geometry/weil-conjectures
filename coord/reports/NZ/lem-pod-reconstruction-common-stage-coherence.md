# Stage-1 delivery: lem-pod-reconstruction-common-stage-coherence

## Files written

- dag/nodes/sec-six-functors/lem-pod-reconstruction-common-stage-coherence.json: statement, split into seven explicit calculation steps; not a Mathlib leaf.
- citations.json: verbatim statement excerpts for every (step, cited node) pair.
- report.md: this report. No new DAG nodes and no Mathlib leaves.

## Attachments

None. Searched the exact blueprint tag and reconstruction, completion/scalar and common-stage terminology in lean/WeilConjectures. Existing common-stage and Poincare-duality transport modules do not state all clauses with the actual completion unit and specified comparisons. In particular Transport.lean discusses pairing/reduction transport, not this natural transformation. No Lean file was written and no compiler was run.

## WANTED

None. The blueprint and Bhatt--Scholze source were available. The proof is marked agent-written: the source's one-sentence identity assertion does not contain this coefficient-coherence calculation.

## Problems and corrections

The imported item had no proof. Its statement, statement dependencies, source, creation metadata and blueprint ancestry are retained. No statement dispute was found. The key issue was to use the actual quotient-cone comparison, rather than define a new comparison to make coherence hold. The existing integral intertwining statement supplies that map; its existing raw-rational successor supplies its rationalization and naturality on every rational arrow. The proof derives the conjugation formula from these statements and cancels isomorphisms. It does not use the proof of either unsplit dependency.

The wording “identity compact-support functor” means the compact-support functor attached to the identity scheme map, naturally isomorphic to the category identity; its object formula is generally a reconstructed object, not literal equality of objects. The last paragraph of the unchanged item states precisely that natural isomorphism.

## Sources and searches

Read coord/brief-stage1.md, stages/1-dag.md, SETUP.md (including all three blueprint levels), GOAL.md, the worker role, chapter sec-six-functors and unit sk-thm-sf-package. Read both copies of delivery-errors.md B--E. No released repair note exists, and the sandbox initially contained only dispatcher brief markers, so there was no old split/report to discard.

Read literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/lem-pod-point-dualizing-complex.proof.md, especially its first sentence. Read Bhatt--Scholze Definitions 3.5.2--3.5.3, Lemma 3.5.7 including the regular-ideal unbounded clause, and Lemma 6.8.2(1) from the local PDF. These justify the context of the existing reconstruction interfaces; the new proof is an explicit categorical calculation over their statements, not a theorem attributed verbatim to Bhatt--Scholze. No SGA source is used.

Searched the whole imported blueprint with blueprint_refs.py search for coherence, reconstruction and common-stage, and the live DAG for intertwining, scalar associators and common-stage functors. Existing raw naturality, actual integral intertwining, scalar composition, common-stage category and compact-support definition suffice. The generic point-fiber descent/transport nodes involve additional fiber functors or point automorphisms and are not exact attachments for this item. No new node was needed. The existing definition def-weil-algebraically-closed-coefficients explicitly supplies the representative equality criterion and composition over a common field.

Retained and read all six inherited Mathlib search results, including the second completion phrasing and the successful Functor.associator query. Ran four additional searches with msearch.py (recorded verbatim in searches.jsonl and mathlib_searches): LeanFinder with the general conjugation/descent formulation, Loogle for NatTrans.naturality plus Functor.associator, grep in CategoryTheory for common-stage/reconstruction/completion-scalar terms, and LeanSearch for derived-completion coefficient-stage descent. Read the generic associator source at CategoryTheory/Functor/Category.lean:185 and the module-scalar pseudofunctor in Algebra/Category/ModuleCat/Pseudofunctor.lean. Their contexts are ordinary functors or modules; they do not assert the project's actual quotient-cone comparison equation. Other returned Dold--Kan/eventual-constancy and uniform-space completion declarations are unrelated by their displayed types. There is no exact match or one-line specialization for this item.

## Not duplicates

No new nodes. The elementary cancellation and conjugation equations remain proof steps. The existing raw-natural statement is a dependency, not a duplicate: it proves one coefficient square and finite-stage naturality, whereas this item derives its scalar-associator law and common-stage representative calculus.

## Review by NZ

I checked the source sentence against the actual statement: the item expands only the coefficient and common-stage part of identity compact support. Its geometric context is the point s over the algebraic closure, with ell invertible, and every field is a finite subextension of the fixed algebraic closure. This stays on the unit's identity-compact-support route. There are no new statements to test or new sources to request.

Step 1 uses the statement of lem-pod-reconstruction-raw-rational-naturality for agreement with identity compact support, the rationalized actual beta, inverse u/v components and its scalar square. The statement of lem-pod-completion-unit-scalar-intertwining explicitly specifies the same-index map, its completed conjugation, and equality with the actual unit square, including ramified extensions. Thus the proof does not replace the supplied comparison by an arbitrarily normalized one. I checked the domain of beta is S(H_E C), its target H_L(S C), and both sides of the square land in S C. All input objects are complete because they are objects of the stated raw rational categories.

Step 2 uses inverse naturality from the raw lemma and the canonical scalar units from lem-weil-scalar-extension-composition. The written two naturality equations have domain S(H_E C) and common codomain C; cancelling v yields exactly the unit equation, including non-strict scalar units.

Step 3 uses those same two statement nodes. Both composites have source UT(H_E C) and target H_M(VC); postcomposing with v at VC makes both equal a_C UT(v_C). I checked naturality of the given scalar associator is asserted by the cited statement, rather than borrowed from its proof. Only an invertible v component is cancelled. Consequently the calculation applies to successive ramified extensions without a finite-projection detection argument.

Step 4 uses the raw lemma's naturality for arbitrary rational h, not just integral arrows. The inserted v and u are evaluated at the actual objects S_{F/E}C and S_{F/L}D. The result t_Y^{-1} h t_X has precisely the endpoints required for a morphism between reconstructed objects. Every inverse is of a declared natural isomorphism.

Step 5 uses lem-weil-scalar-extension-composition for naturality of the associators and def-weil-algebraically-closed-coefficients for transition conjugation and eventual equality. I wrote out both endpoint associator squares and the transition equality; this is the concrete argument behind representative independence. It does not assume a preferred common field. For unrelated representatives, their equality supplies a further field by the definition; for two initial common fields their compositum is available in that definition.

Step 6 uses the same common-stage definition for identities and composition, the compact-support definition for its object at a finite stage, and the raw lemma for its agreement with H_E. At a common field the middle t_Y cancels, proving composition; the identity cancels t_X with its inverse. This supplies arrow-level functoriality, which the compact-support definition explicitly leaves to a separate statement. It does not falsely cite that definition as already proving independence.

Step 7 uses inverse/naturality from the raw lemma and extension of morphism representatives from the common-stage definition. The component of [E,v_C] at F is t_X, so its naturality equation is exactly the calculation of Step 4. The inverse [E,u_C] is two-sided already at E. Step 5 supplies persistence under every further extension. This checks every clause, including the actual displayed naturality equation.

For B--E, I verified every used non-elementary input is one of these existing statement interfaces and every citation quote is literally in its statement (C1/C4); proof_deps is the union of uses. All remaining operations are displayed naturality, associativity and inverse cancellation, hence elementary relative to those interfaces. No new nodes restate clauses, hide proofs, or duplicate existing nodes (B/D). Tested E=L=M, zero objects, identity/zero arrows, composition at unequal initial fields, sums/fraction-valued rational arrows, and further ramified extension. All equations retain the stated endpoints and hypotheses (E). No step exceeds 2000 characters. The only off-unit statement tool is scalar-extension-composition, declared in split_report.tool_uses because it supplies generic coefficient associators rather than replacing a unit step. The source, statement and inherited search records are not silently rewritten.

## Unfinished work

None in this one-level split. The pre-existing unsplit intertwining and raw-rational dependencies remain separate queue items.
