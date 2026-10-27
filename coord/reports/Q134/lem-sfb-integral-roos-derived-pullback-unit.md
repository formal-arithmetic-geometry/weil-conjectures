## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-integral-roos-derived-pullback-unit.json: item, statement; ten-step split, no Mathlib match.
- citations.json: 29 entries, one verbatim statement excerpt for each step/node citation.
- report.md: worker report and signed review.

No new nodes; no Mathlib leaves. The statement, statement dependencies, source, created record and other maintainer-owned fields are preserved. All writes were to this sandbox; no Lean, compiler, Lake or repository git commands were used.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag, Roos, derived completion, and completedPullbackComparison. The exact tag has no hit. Existing Roos results are generic, and the integral reduction/completion theorem is about the étale reduction of a completion unit, not this pro-étale pulled augmented strict tower and its two scalar categories. None states every clause of this item.

## WANTED

None for this split. Existing coefficient-ring input lem-weil-l-adic-extension-integers-dvr has its own recorded Serre reference; this split cites its statement and does not claim to have read that unavailable book.

## Corrections and omissions

The item statement is unchanged; no statement dispute was found. Its empty proof was replaced. The important potentially invalid shortcut is deriving a finite quotient as though P tensor S_n were K-flat over the completed ring. Step 5 instead proves that the exact pullback on the whole strict-tower category preserves all quasi-isomorphisms, so the supplied resolving-class replacement compares to the actual tower T. No exactness of tensoring arbitrary quotients is used.

No work is left unfinished. The blueprint's first paragraph and its constant-scalar comparison paragraph are the route throughout. We do not use any SGA source. The unit and chapter records need no edits: the item is a child realizing part of the inverse-image step, not the key node stating that unit.

## Searches and reuse

There was no pre-existing item, report or citations file in the sandbox. Read all five searches.jsonl results after running the authorized search commands. The item already carried the O3 searches; those are retained, and only the five actually executed Q134 searches are appended. LeanFinder was tried with two different phrasings. Loogle returned presheaf pullback adjunctions/composition; LeanSearch returned ordinary adic completion and abstract limit existence; LeanFinder returned ordinary completion, local cohomology and abstract homological/category results; source grep for Roos, derivedCompletion and KFlat returned no hits. These do not prove this item's normalized unbounded sheaf-complex assertion. All services answered successfully; no unavailable result was called a negative search.

DAG searches by strict-roos, completion-equivalence, kflat, scalar-balancing, pulled-reduction and the source tags found the existing inputs now cited. Blueprint searches for Roos, completion unit, finite projections, pulled quotient and derived completion found only general ingredients and the completed-pullback definition, not an equivalent statement of this full item; same_as remains empty. No new node is proposed, so no same-tag pair needs a Not duplicates entry. A local dependency traversal of every proposed tool found no path back to the item.

## Not duplicates

No new nodes. In particular, reuse lem-sfb-integral-augmented-quotient-towers for the ordinary generator-normalized comparisons, lem-sfb-augmented-scalar-roos-resolution for scalar restriction and augmented resolution normalization, and lem-weil-strict-roos-comparison for the exact-product one-ring comparison. Do not repackage any of their clauses as new nodes.

## Review by Q134

I read AGENTS.md, GOAL.md, SETUP.md including its three blueprint levels, the stage-1 brief, worker role, full stage-1 document, tools field-ownership rules, and both copies of delivery-errors B through E. I read the chapter and sk-lem-int-tensor unit records, then the current main-20261015 det-lem-int-tensor-pullback proof. For the mathematical source I read Stacks proetale.tex lemma-naive-completion (099M) and lemma-pushforward-Noetherian-case (099N), including their proofs; sites-modules.tex lemma-completion-flat (093M); sites-cohomology.tex lemma-pullback-K-flat (0G7E), lemma-pullback-tensor-product (07A4), the K-flat derived-pullback construction, and lemma-derived-limit-is-ok (0941); derived.tex lemma-products (07KC); and algebraization.tex proposition-derived-completion and lemma-restriction-derived-complete-equivalence. The strict signed cochain refinement is marked agent-written. There are no new nodes requiring additional source review.

For Step 1 I checked the full coefficient-ring and integral-limit statements. The DVR node explicitly says PID, the chosen uniformizer is nonzero, and the finite coefficient definition explicitly says finite quotients. A PID is Noetherian since its ideals have a single generator; the two-term pi^n resolution proves the needed perfectness. This verifies every algebra hypothesis before applying the general adic interfaces, without an extra assumption on E or on P.

For Step 2 I checked the actual definition of alpha_g as the component of the natural pullback-from-point isomorphism. Its naturality for A to A/pi^n proves the finite projection equation, and the limit universal property proves c_g equals alpha_g. The integral-limit statement gives the canonical ring presentation. The Cartesian coefficient theorem really states exact module pullback, not just an isomorphism of rings. The same functorial construction applies to the discrete condensed ring A for C; no topology on A was silently changed for R.

For Step 3 I checked that constant-completion-equivalence explicitly states flatness of the completed ring over the constant ring, and that flat-scalar-restriction-kflat states both K-flatness and flat terms. Ringed-topos-kflat-pullback likewise states both properties for any ringed-topos morphism. The sites are the chosen small pro-étale skeletons and the coefficients are commutative. These inputs have no boundedness, constructibility or completeness hypotheses.

For Step 4 I read the complete strict-quotient-completion-data definition: it chooses the universal derived strict quotient construction, its comparison is invertible on flat-term K-flat models, and its normalization identifies the actual unit. This is more than a per-level tensor assertion. The scalar-tower-realization statement separately fixes the derived scalar-extension units and transitions, with the two displayed epsilon equations; those are exactly what is used. I checked the n+1 versus positive-integer indexing. The adic coefficient datum constructs the same strict tower on a K-flat model, so no unrelated choices of representatives are identified.

For Step 5 I read the levelwise-abelian and diagram-kflat-replacements statements, not their proofs. Kernels/cokernels of towers are levelwise, so exact g_R^* preserves their cohomology and tower quasi-isomorphisms. The strict replacement has the required compatible maps, not independent level replacements. Consequently the derived pullback compares to T even though finite quotients may fail to be K-flat over R_Y. The definition of completed pullback specifies the augmentation from the constant tower on the K-flat input, which fixes the map as well as its target.

For Step 6 I checked the entire statement of integral-augmented-quotient-towers. It explicitly gives lambda, theta, d, the constant comparison V to the quotient tower of g_C^*Q, their pure-tensor formulas and the two strict augmentation equations. Thus the step does not take a theorem from that node's proof or invent a compatibility. It applies even to finite tensors that are not K-flat. This existing node remains an independent unsplit input, not an attachment.

For Step 7 I checked the product-exactness statement for arbitrary commutative ring sheaves on the small pro-étale site; it applies to both R_X and C_X. The strict Roos statement explicitly assumes exact countable products, gives the K-injective normalization with zero shifted component, and identifies compatible strict augmentations with the canonical derived augmented map. I computed D(0,b^Pi z) with the supplied sign convention; its first component is zero because (1-s)b^Pi=0. I have not attempted to deduce equality of maps to a derived limit merely from equality of finite projections.

For Step 8 I checked the last paragraph of constant-completion-equivalence: it explicitly gives the Koszul/quotient comparison over each of constant and completed coefficients, identifies it with actual derived completion, and preserves units on arbitrary inputs. This supplies both required derived-category isomorphisms. It is stronger than the mere equivalence of complete subcategories in the first paragraph, and that weaker assertion alone would not justify the step.

For Step 9 the completed-pullback definition itself fixes the constant-tower unit followed by Rlim of the pulled augmentation. The normalized strict-Roos theorem fixes exactly this map. I wrote the diagonal product calculation using lambda b_T=b_U; no unspecified cone filler or sign change is used. The claim is only called the defined completed-pullback comparison on its complete-input domain; the augmented construction exists for arbitrary P.

For Step 10 I read the whole augmented-scalar-roos-resolution statement and checked its source is a generic arbitrary-ring-map strict cone calculation, not a restatement of this item. It explicitly identifies restriction/product coordinates, its augmentation identity, and its derived normalization. Substitute theta and d_P using the stated strict equation; it gives the constant completion unit by Step 8. Constant-completion-equivalence and the completed-pullback definition then give precisely 099N(2),(5) on complete inputs. The ambient D(R_X) and D(C_X) remain distinct throughout.

I checked delivery-errors B1--B10: there are no new nodes, fabricated searches, unsupported leaf declarations, unnamed objects or blueprint omissions. For C1--C8 each non-elementary input is an opened node statement and each use has a verbatim citation; dependencies are their union, no cycle is introduced, and off-unit generic tool uses are explained in split_report.tool_uses. For D1--D5 the proof gives the coefficient naturality, exact tower argument, augmentation equations and completion-unit assembly; it does not move the item into a new node. For E1--E7 all hypotheses were checked as above, the two coefficient categories and strict towers were kept distinct, and no source statement was silently weakened. All ten steps are below 1,100 characters, so none hides a long unreviewed comparison.

Small cases: g=id gives the ordinary quotient completion unit; P=0 gives zero towers and zero maps; P=R_Y[0] gives the ring coefficient tower; arbitrary shifts or unbounded P use the same degreewise equations; X empty gives zero module categories; a noncomplete P (e.g. a countable free sum at the point) is allowed but its completion unit is not asserted invertible. In particular source completeness would not by itself prove target completeness, and this item makes no such assertion. No new statement required a counterexample repair.
