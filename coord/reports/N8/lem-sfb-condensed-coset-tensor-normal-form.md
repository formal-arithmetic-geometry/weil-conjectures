# Stage-1 report: lem-sfb-condensed-coset-tensor-normal-form

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-condensed-coset-tensor-normal-form.json: statement item, now split into seven explicit elementary steps. No statement change; no new nodes; no Mathlib leaves.
- citations.json: verbatim statement extracts for each proof-step citation.
- searches.jsonl: actual msearch.py searches, retained as produced.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag and for coset/tensor/normal-form and sectionTensor terminology. The hits concern other scalar tensor comparisons or unrelated cosets. The relevant lean/Sheaf/CategoryTheory/CondensedSplitCosetInduction.lean is a definition/statement of the consuming induction theorem; it is not a completed upstream proof of this item.

## WANTED

WANTED: an external reference proving the sectionwise balanced-tensor normal form for internal condensed subgroup induction, including naturality for semilinear restriction maps and noninjective maps of coset indices, for lem-sfb-condensed-coset-tensor-normal-form. The item's recorded source already labels this an agent-formulated input. I read the current blueprint direct-image stability proof, paragraph (3); that paragraph motivates the consuming exact-induction input but does not contain this algebra calculation. The proof is therefore explicitly agent-written. No SGA source is used.

## Corrections and outstanding work

No mathematical statement correction was required. The empty proof is replaced with the actual factorization and finite-sum argument. The existing statement dependencies and all maintainer metadata are retained. The current unit record is historical and names the earlier chapter; this worker does not rewrite it. The ancestor search prints None, agreeing with the existing blueprint.from.node=null. The existing from.place identifies paragraph (3) precisely and is retained. No unit realization fields belong to this auxiliary node.

No unfinished argument in this one-level split. This does not assert any Lean proof. The outstanding external literature request remains explicit.

## Searches and reuse

Read the imported Mathlib search records and their candidate, then ran six fresh logged searches through msearch.py: two LeanFinder phrasings, LeanSearch, Loogle for Rep.coinvariantsTensorFreeLEquiv, and two grep queries. All services answered. Read Mathlib/RepresentationTheory/Coinvariants.lean:450-519 (especially coinvariantsTensorFreeLEquiv:503), RepresentationTheory/Induced.lean:46-89, LinearAlgebra/DirectSum/TensorProduct.lean:32-104 and LinearAlgebra/DirectSum/Finsupp.lean:30-100. The representation result concerns diagonal coinvariants of an abstract representation tensored with a free representation. It does not immediately specialize to the subgroup-balanced tensor presheaf, continuous sections, changing test rings, and restrictions merging coset indices. Tensor/direct-sum distribution similarly does not state the item. No Mathlib match was claimed.

Searched the whole DAG for coset normal forms, balanced tensors, tensor universal properties, finite-support linear maps and direct sums; read the nearby split-coset induction, action definition, balanced-tensor finite-free comparison, and tensor-relation section quotient. The last two concern respectively internal mixed bimodules with finite free coefficients and commutative algebra sheaves on schemes, not this construction. Blueprint searches for coset, balanced tensor, tensor product and direct sum found no imported equivalent. No new node is introduced: each candidate subclaim is an explicit use of the definitions and finite sums, not a lemma concealed behind a citation.

## Not duplicates

No new nodes. The item is not a restatement of lem-sfb-condensed-split-coset-induction: it proves the algebra normal form used to prove kernel preservation there, and does not assert an induction adjunction or sheafified exactness. It does not cite that consumer, so there is no dependency cycle.

## Review by N8

I read the source paragraph (3) named above, the chapter route, the unit record, the current item, and all three statement dependencies. The condensed-ring definition makes A(S) a commutative section ring and supplies ring restrictions; the size convention bounds the site; the action-module definition supplies exactly the sectionwise linear group actions, their compatibility with restriction, and equivariant coefficient morphisms. No geometric or derived theorem enters this algebra calculation. There are no new nodes with additional sources to review.

Step 1 is pointwise right-coset equality and continuity into a subspace. The identity s(q(p))^{-1}p lies in H uses right cosets pH, not left cosets Hp or normality. I wrote out both composites and the precomposition identities. There is no assumption that s sends the identity coset to 1. Step 2 cites def-sfb-condensed-action-module for the R-linear group action, and expands arbitrary finite group-ring sums to show that the displayed group-element relation is exactly full group-ring balancing. It uses the defining universal property of the balanced tensor, not a flatness or tensor exactness theorem. Step 3 expands a finitely supported family as its finite sum of singleton families; its pushforward formula gives the coefficient sum over a finite support, so it is valid for a noninjective index map. These are elementary presentations, not new nodes.

Step 4 cites the same action definition for linearity and the multiplication law. I checked x_(pk)=x_p and h_(pk)=h_p k, in that order, before descending alpha; beta is a finite sum. Step 5 uses that cited action law for the identity action and uses precisely the relation from step 2 to compute beta alpha. Both composites are computed on generating symbols, and generation has already been justified, so there is no unstated normal-form lemma. Step 6 cites naturality in all profinite S from the action definition. It verifies restriction preserves each balancing relation, and defines the restriction of D by the explicit sum that adds coefficients when indices collide. Identity and composition reduce directly to substitution and the presheaf identities of A and M. Step 7 cites both natural actions and the definition of equivariant coefficient morphisms. I checked the two restriction squares on their respective generators and wrote u(hm)=h u(m) explicitly for coefficient naturality. Every citation is supported by a full verbatim statement sentence in citations.json. All uses are in proof_deps.

I checked the zero ring and zero module (all coefficients vanish), H=P (one coset index and an arbitrary representative still cancels), H=1 (free group-indexed sum), infinite X (only finite support is ever summed), and the empty test (P_S,H_S,X_S each have one continuous map, and sheaf sections are zero modules). For non-normality I also ran a finite calculation with P=S3, H generated by a transposition, the nontrivial H-action on F5, and an arbitrary coset section: all 60 balancing tests and the inverse factorizations passed. A two-point test restricted to one point gives two equal indices and correctly adds 2+4=1 in F5. The symbolic proof handles general coefficient restriction maps by semilinearity, with no assumption of sectionwise epimorphism or local constancy.

I checked delivery-errors B-E: no new unsplit node with hidden proof, no duplicate or clause shifted into a new node, no borrowed theorem absent from a cited statement, no added hypotheses, no sheafification/exactness claim borrowed from the consumer, and no normality, finite-index or discreteness assumption. Every step is under 700 characters, so no long step hides a separately sourced lemma. The generator presentation, both inverse checks, and both naturalities are written out rather than described as standard.
