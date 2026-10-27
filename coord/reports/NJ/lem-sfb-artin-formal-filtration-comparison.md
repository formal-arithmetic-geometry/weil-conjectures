# NJ stage-1 delivery: lem-sfb-artin-formal-filtration-comparison

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-artin-formal-filtration-comparison.json: existing statement, now split into six explicit steps; not a Mathlib leaf.
- citations.json: seven verbatim quotations, one for each step/node pair.
- searches.jsonl: actual searches made by the required msearch command. The existing item's earlier searches remain in its JSON, and the additional queries and verdicts are appended.
- report.md: this report.

There are zero new nodes and zero new Mathlib leaves. The existing quotient-Artinian-local Mathlib leaf supplies the ring-theoretic prerequisite. The inverse equivalence, its isomorphisms and the evaluation formulas are proved in the item, rather than moved into replacement lemmas.

## Attachments

None. Searches for the exact blueprint tag and for formal objects, cofibred categories and formal-filtration comparison in lean/WeilConjectures found no declaration of this result. AdicTowerSequence and Artin-Rees tower results concern module systems, not arbitrary groupoid-valued deformation categories, so they do not attach.

## WANTED

None. All mathematical sources used are available in literature/stacks-project/.

## Statement dispute and corrections

STATEMENT-DISPUTED: the last sentence said "any local map C to A", but the functor is defined only on local R-algebra maps inducing the identity on the fixed residue field. Without that condition the purported transport is undefined. For an explicit type check, take R = F_2, k = C = A = F_4, every I_n = 0, and the Frobenius map C to A. This map is local, is R-linear, and factors through every C/I_n, but induces the nonidentity automorphism of k; it is not a morphism of the specified test category. Therefore an arbitrary pseudofunctor on that category has no transport along this map. Requiring a local R-algebra map inducing the identity on k restores the exact intended assertion of Stacks 06H6, where all maps lie in the test category. The "pullback along C to C/I_n" wording is also made "value at C to C/I_n", consistent with the covariant ring-map transport convention. No hypothesis on F, no cofinality requirement, and no equivalence or compatibility clause has been weakened.

The source's proof of Tag 06H6 explicitly omits verification of the equivalence. Steps 3 and 4 give the inverse and both natural isomorphisms; steps 5 and 6 supply the evaluation compatibilities needed by the parent. These are proved here, not assumed as an omitted "standard" argument.

The existing blueprint provenance has from.node = null; tools/blueprint_refs.py ancestor reports None for this item. Its from.place and via chain nevertheless explicitly identify the original direct-image alteration route and the intervening Artin versal-formal-object argument. I retained this existing provenance rather than invent a blueprint ancestor. The recorded originating node name det-thm-sf-ctf-stability-direct-images is not a file of literature/blueprint/latest/. Searches of the whole imported blueprint for "formal objects", "cofinal filtration", "formal", "cofinal" and "Artinian local" found no competing statement. In particular ordinary formal power series and adic coefficient systems are different notions. The parent lem-sfb-artin-rs-versal-formal-object, step 4, uses precisely this comparison and its evaluation clause; no unit/chapter route is replaced. I read dag/chapters/sec-six-functors-basics.json, dag/units/sk-thm-sf-ctf-stability.json and the current latest unit text.

## Not duplicates

No new nodes. In particular lem-weil-pbc-noetherian-local-quotient-artinian-local is reused rather than duplicated. The other live 06H6 occurrence is the parent lem-sfb-artin-rs-versal-formal-object, which asserts existence of a versal object using RS and finite-dimensional tangent space, not independence of filtration for arbitrary cofibred groupoids.

## Review by NJ

I read formal-defos.tex, definition-formal-objects (Tag 06H3), lemma-completion-cofibred (06H4), definition-completion (06H5), and the complete statement and proof of lemma-formal-objects-different-filtration (06H6), including the paragraphs defining systems for an arbitrary ideal filtration. I also read algebra.tex, lemma-Noetherian-dimension-0 (00KH) and lemma-artinian-finite-length. There are no new-node sources to check. The proof is marked agent-written because it adds the details the Stacks proof omits.

For step 1 I opened the entire statement of lem-weil-pbc-noetherian-local-quotient-artinian-local. It applies with C Noetherian local, a positive exponent supplied by cofinality, and I_n proper, hence contained in the maximal ideal. It states Artinianness, locality, and the maximal ideal of the quotient, exactly the facts used; it does not require a finite residue field. The specified residue field of each quotient is inherited from C. The other cited statement, def-sfb-artin-deformation-test-category, explicitly defines objects and maps of the test category. Thus the quotient maps used really lie in its domain. The recursive choices of p and q use the two stated directions of cofinality and the decreasing filtrations, with indices also bounded below by their arguments; these inequalities are essential to both inverse comparisons.

For step 2 I opened the definition node's pseudofunctor clause: it gives covariant transport functors with coherent identity/composition isomorphisms. The construction uses that clause, not RS or versality, which the same node defines separately. I checked the directions of all inclusions and quotient maps. The transition formula comes from the supplied system's transitions, and the displayed transition identity proves composition; the arrow squares are obtained by applying the same functor to the original square. The definition does not assert this comparison theorem: its entire construction is written in the step.

For step 3 the same cited transport clause permits the functor G and the comparison of its composite with E. The isomorphism from GEu at n to u_n is the original transition from p(q(n)) to n, which exists because p(q(n)) is at least n and I_p(q(n)) is contained in m^q(n), hence in I_n. Both transition-square paths are identified with one explicitly named original transition, including transport composition isomorphisms. Naturality is exactly the arrow square of the given compatible family. No faithfulness of individual transport functors is assumed.

For step 4 the definition node's formal-system clause is exactly what supplies the transitions from q(p(r)) to r. The ideal containment is m^q(p(r)) contained in I_p(r) contained in m^r, so this comparison has the correct source and target. The two comparison paths are again the same original transition. This proves a second natural isomorphism, not merely objectwise essential surjectivity. Two inverse functors up to natural isomorphism exhibit the claimed equivalence by the definition of equivalence; no separate cofinality or 2-limit theorem is silently cited.

For step 5 I checked the definition node's actual evaluation sentence: evaluation is transport of any sufficiently high truncation. Choosing r at least q(n) makes m^r contained in I_n, so the evaluation at B_n is legal. The formula states the actual isomorphism to u_n. Its compatibility under increasing r and under n' at least n is proved by the displayed transition identity, rather than asserted by "transport compatibility". Naturality for system arrows is checked by their original component square.

For step 6 the same evaluation sentence and the already established step-5 isomorphism suffice. Factoring a through B_n ensures that a kills m^r at the chosen r. The induced map B_n to A is local, R-linear, and residue-preserving under the corrected hypothesis, so transport exists. This is an elementary composition of the previous isomorphism with one transport functor. A common larger index compares any two factorizations, and the transition identity from step 5 proves equality. Thus there is no separate non-elementary lemma hidden here.

I tested C = k (maximal ideal zero, every proper I_n zero), a nonzero Artinian complete local C (eventually constant zero filtrations), the usual I_n = m^n, and repeated ideal levels. The construction allows repeated indices and identity transitions in every case. Cofinality excludes a constant nonzero ideal in a separated non-Artinian complete local C; no invalid such example is used. Taking a constant groupoid with a nontrivial automorphism group confirms that the argument must retain arrow data: it does, through the naturality and transition squares. The field need not be finite, F need not satisfy RS or be a predeformation category, and the proof invokes none of these extra hypotheses. Every non-elementary step is below 2000 characters; no independent lemma is hidden in a long step.

Against delivery-errors B--E: no new statement-only nodes or Mathlib matches are fabricated; the only extra theorem is an existing leaf with its full statement read. All seven citations have verbatim statement quotations in citations.json. No tag is substituted for a missing theorem, no source-proof internal object is borrowed, no node repeats a clause of the item, and no new dependency can form a cycle through the item (the definition node and existing Mathlib leaf do not depend on it). The proof writes the omitted inverse and both compatibility verifications explicitly. All source and search reads were read-only; no Lean was written and no compiler, Lake or build tool was run.

## Incomplete work

None in the mathematical split. Validation and delivery are recorded by the required delivery command.
