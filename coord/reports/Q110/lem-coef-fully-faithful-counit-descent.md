# Worker report: lem-coef-fully-faithful-counit-descent

## Files written

- dag/nodes/sec-six-functors/lem-coef-fully-faithful-counit-descent.json: existing statement, now split into eight elementary steps; no exact Mathlib match for the whole diagram.
- citations.json: empty list, since no proof step invokes another node's theorem. The statement dependency defining the adjunction remains unchanged.
- searches.jsonl: five actual searches, using LeanFinder (two phrasings), Loogle, grep and LeanSearch. Existing inherited search records remain in the node.

New nodes: 0. New Mathlib leaves: 0. No Lean source, compilers, Lake, live repository writes or manual git commands were used.

## Attachments

None. Searches of WeilConjectures for the exact blueprint id, counit/descent terminology and coefficient/counit combinations found no project declaration with this statement. The generic Mathlib isomorphism-lifting declarations are only ingredients, not attachments of the item.

## Wanted

None.

## Findings and corrections

The item is an agent-written extraction from the closed-immersion calculation in lem-coef-finite-dualizing. I read the parent blueprint in the recorded master path and the current main-20261015 node and proof at sec-smooth-purity/sk-lem-sp-tower/lem-coef-finite-dualizing.{md,proof.md}. Both give the same local-map/global-adjoint requirement. The parent retained split, step 15, applies precisely this categorical descent. The chapter and unit records were read; this is not their key node and their records are unchanged. There is no blueprint_update on the item.

The current item already incorporates the maintainer's correction from global natural transformations to delta_A at one object and delta_B on a full subcategory containing the two needed objects. I preserved this statement verbatim, including its restricted domains. No statement dispute or route change is needed. In particular, the proof does not assume coefficient extension preserves bounded-below objects.

Searches of the whole DAG and blueprint for fully faithful and counit facts revealed general tools and geometric comparison statements, but no equivalent blueprint node. The exact new-node ancestor query returned lem-coef-finite-dualizing. The blueprint ancestry and its specific closed-immersion place were retained, with same_as empty.

I read Mathlib/CategoryTheory/Functor/FullyFaithful.lean, including the definitions Full/Faithful, the preimage construction, and preimageIso, and the whole Mathlib/CategoryTheory/Adjunction/Restrict.lean. The latter requires a global primed adjunction and globally commuting functor isomorphisms, unlike this item, and does not supply the coefficient diagram. preimageIso handles only lifting h; that lift is written directly in two lines from bijectivity and does not justify creating a new node. All five searches succeeded; their queries and result digests are recorded as actually run. The pre-existing searches were retained rather than falsely attributed to this run.

## Unfinished work

None in the mathematical split. The independent maintainer review follows delivery.

## Review by Q110

I checked the item against the two blueprint versions named above and against the parent retained split's step 15. The source leaves this as the assertion that the local map is the adjoint map; this delivery supplies that assertion's elementary diagram chase, marked proof_origin.by = agent. I also read Stacks categories.tex, definition-faithful (tag 001C), and the full-subcategory definition immediately following it: full faithfulness is bijectivity on Hom sets and fullness includes all ambient morphisms between the objects. This makes the lifting proof a direct use of a hypothesis's definition, not a hidden general theorem.

Step 1 defines abbreviations for objects already in the statement and forms h from three isomorphisms. Functors preserve inverses by applying them to the inverse identities; there is no extra lemma being assumed. All factors have the asserted domain and codomain.

Step 2 lifts h and its inverse using the assumed Hom bijections and proves the two inverse identities by their injective endomorphism maps. It also proves uniqueness. I checked that the full subcategory on which S_C,B is fully faithful can differ from C_B^0: both contain X and Y, so this is harmless.

Step 3 uses only the given B-counit equality and naturality of delta_B at b. Since C_B^0 is full and contains X and Y, b lies in its naturality domain. The displayed composite L has source S_D,B T_D F_A N and target W. No unbounded comparison is introduced.

Step 4 substitutes the exact prescribed image of b. Naturality of E at t gives t E_W = E_Z H(J_B(t)); composing with the two inverses gives exactly E_W H(J_B(t)^{-1}) = t^{-1} E_Z. I checked that W and Z, together with t and its inverse, lie in the full subcategory V_B. J_B is never evaluated outside it.

Step 5 substitutes the coefficient square and the counit equation for b', each exactly as written in the hypotheses. The inverse c'_Q exists by the component hypothesis. No naturality at an additional object or coefficient-flatness hypothesis is used.

Step 6 uses naturality of c' only along alpha_A and cancels c'_Q. Its remaining factors are exactly T'_D(E_A F'_A(alpha_A) delta_A,N). Step 7 substitutes the A-counit equality and uses naturality of t_D at e_A,M to identify this with S_D,B(T_D(e_A,M)). Both are direct equalities from the statement, with rightmost-first composition consistently maintained.

Step 8 precomposes with S_D,B(c^{-1}) and then applies injectivity on Hom(F_B T_C N,M_B), exactly the Hom set assumed in the item. It never uses faithfulness elsewhere in D_B. This closes the actual counit identity, not just an isomorphism of objects. The extra invertibility hypotheses on delta and c'_U are harmless stronger hypotheses; the written calculation does not need all of them. I did not weaken the item by removing them.

Every step has uses = [] and elementary = true because it is one explicit substitution, inverse cancellation, or the two-line lift from Hom bijectivity. There is no cited-node theorem used without its statement. I opened the unchanged statement dependency lem-weil-pbc-adjunction-of-natural-bijection: it states the natural Hom bijection, unit and counit formulas and triangle identities. Those explain the terminology in the statement; no additional adjunction identity from that node is needed in the proof. Thus there are no proof citations to quote and citations.json is correctly empty. No step exceeds 2000 characters; none hides an intermediate comparison lemma or a standard geometric argument.

For edge cases, I checked the terminal category, identical coefficient and comparison functors (all comparisons identity), and one-object group categories where composition is noncommutative. The latter checks the order of inverse factors in h, naturality of E, and c'. The inverse lift uses endomorphism faithfulness as well as Hom(X,Y) faithfulness, which the stated full-faithfulness hypothesis supplies. The restricted delta domain still suffices when the two full subcategories differ. There is no empty-category instance with the fixed object M, and no assumption of nonzero objects, additive structure, finite coefficients, or abelian categories. Categories with zero objects and zero coefficients present no obstruction. The proof is independent of all such extra structure.

I checked B--E of delivery-errors: no new statements or duplicate nodes, no hollow data, no moved clause, no theorem invoked merely by tag, no circular dependency, and no SGA source. The statement and its hypotheses are unchanged; the correction here is filling its previously empty proof with the complete calculation.
