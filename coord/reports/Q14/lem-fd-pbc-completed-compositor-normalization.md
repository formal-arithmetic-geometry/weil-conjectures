# Q14: lem-fd-pbc-completed-compositor-normalization

## Files written

- dag/nodes/sec-fourier-transform/lem-fd-pbc-completed-compositor-normalization.json: statement item split into seven proof steps; not a Mathlib leaf. The statement, source, original blueprint ancestry, and original searches were retained. New nodes: 0. Mathlib leaves: 0.
- citations.json: one exact statement quotation per cited node per step (20 entries).
- searches.jsonl: searches made by the required msearch.py command. The five new queries supplement, without discarding, the imported queries.

## Attachments

None. Searched lean/WeilConjectures for the blueprint id, completed compositor, completionUnit/completion_unit and pullbackComp/conjugation concepts. CompletedExchange.lean defines ordinary-to-completed pullback and completionUnit, but does not state all the item's normalized framework/PBC identities. Those definitions are not an attachment of this item. No Lean was written or compiled.

## WANTED

None. The proof is marked agent-written: the blueprint's final sentence motivates the comparison but does not prove its normalization. The necessary human source for the general completion and ordinary composition facts is available locally.

## What needed repair or clarification

The imported item had a statement and searches but no proof. No statement dispute was found and no statement was changed. The important distinction is between the actual adjunction-induced PBC compositor and some isomorphism between its endpoints. A normalization proof must identify the induced adjunction, its quotient unit and its ordinary comparator, not choose an isomorphism after the fact. The existing lem-per-quotient-completed-compositor-unit does precisely this for general morphisms and complete inputs, so creating another lemma for the PBC clause would duplicate it.

For the framework comparison the identity needed is the triangle in the derived category of entire quotient systems. Equality after evaluating at every finite quotient is not used as a faithfulness assertion. The proof explicitly composes the whole-system counit with reduction of the augmentation, obtains e_RK R(u_K)=1, applies whole-system inverse image and realization, and substitutes the specified eta formula. The final two coherence equations are calculated by naturality and precomposition with the specified invertible framework augmentation, on complete inputs only.

## Not duplicates

No new nodes. Whole-DAG and blueprint searches for completion unit, compositor and pullback comparison found no blueprint node stating this full comparison between the two specified presentations. Existing lem-per-quotient-completed-compositor-unit was reused for its strictly more general PBC equation. Existing lem-weil-isomorphism-derived-pullback-comparison-normalization was reused for invertibility of the specified augmentation, rather than creating another completion lemma. Existing lem-pod-reindexing-completion-unit-tensor was reused for reindexing of entire systems and the actual reduction/limit unit and counit.

## Sources and Mathlib searches

Read the current blueprint literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-trace/def-fd-trace-function.md, including its final sentence requiring the PBC coefficient category; the unit and chapter records; Stacks proetale.tex, Tag 099M (lemma-naive-completion) and Tag 099N (lemma-pushforward-Noetherian-case), with their proofs; and sites-cohomology.tex, Tag 0D6D (lemma-derived-pullback-composition), with its proof on a flat-term K-flat representative. The tags were checked in stacks-project/tags/tags. No SGA source is used.

Ran leanfinder twice with different formulations of the full comparison, leansearch once, loogle for CategoryTheory.conjugateEquiv, and grep for conjugateEquiv|leftAdjointCompIso in CategoryTheory/Adjunction. Read the results of all five searches. Read Mathlib/CategoryTheory/Adjunction/CompositionIso.lean lines 25–105 and Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean lines 150–195. These give abstract adjunction conjugation and ordinary module pullback composition. They do not specify the completed pro-etale quotient systems, normalized Roos comparison, or the framework/PBC compatibility, so the item is not a Mathlib leaf. All these executed queries appear verbatim in the item's search records; none of these services was unavailable in this session.

## Review by Q14

I checked the item against delivery-errors B–E with the source and each cited statement open. There are no new statement-only nodes to audit for hypotheses or duplicates. The seven steps carry an argument rather than move the clauses to newly named statements. Each proof step is shorter than 2000 characters. The exact quotes in citations.json are the cited statements themselves, avoiding any claim inferred from a dependency's proof rather than its statement.

Step 1 uses constant-completion-equivalence for transition-compatible reduction comparisons and preservation of the actual completion unit; countable-products-exact supplies the hypothesis of strict-roos-comparison. The latter explicitly states both the K-injective normalization and the zero-shifted-coordinate augmentation identity. The inverse-image comparison definition gives exactly that chosen augmentation. Thus the equation kappa^p=b kappa^s refers to the actual maps on an ambient object. No hypothesis that the ambient object is complete is inserted there.

Step 2 uses the isomorphism-inverse-image statement for exactness, inverse limits and coefficient projections, and isomorphism-derived-pullback-comparison-normalization for invertibility of the specified kappa, not an unspecified isomorphism. The reindexing-completion-unit-tensor statement explicitly fixes reduction/realization identifications and their unit and counit, and identifies the unit on complete inputs. Isomorphism-derived-pullback supplies constructible preservation, while integral-stratified-perfect-characterization identifies the common full integral categories for precisely the noetherian finite-dimensional schemes in this item. The complete-input and constructible-input claims are kept separate.

Step 3 applies quotient-completed-compositor-unit with g=k and h=h. Its hypotheses allow all schemes here and in fact allow arbitrary morphisms. Its P_h is the ordinary completed-ring module pullback G_h here; gamma is the actual quotient augmentation kappa^p, by step 1 and that node's unit-preserving identification. Its hat a is oriented composite-to-single, opposite to c^p; ordinary a is likewise the inverse of c^G. The proof records these orientations and composes with their inverses, then uses naturality at kappa^p_k. Its identity clause supplies the actual PBC identity normalization. This is an elementary substitution of the cited equation, not an inversion of a possibly noninvertible unit.

Step 4 reads the full proetale-derived-pullback-composition statement. It explicitly computes the canonical composition using flat-term K-flat representatives. The coefficient projections and their compatibility with ring homomorphisms are given by isomorphism-inverse-image. The displayed tensor-generator calculation identifies its finite reduction with c_{h,k,n}; it does not presume a second unrelated ordinary compositor.

Step 5 uses integral-pullback-comparison-realization for the exact definition of eta and c^s, including the whole-system counit and the initial zero shifted component. Derived-system-evaluation-calculus states the adjunction and its triangle identities in the derived system categories. Reindexing-completion-unit-tensor identifies the reindexed reduction/realization adjunctions and their actual units and counits. The text writes the relevant triangle e_RK R(u_K)=1, follows it through U_h and realization, and records the remaining termwise composition equation, already proved in step 4. This is why the normalization is an equation of maps of whole systems, not an inference from their separate finite projections. Step 6 is its identity specialization using the specified action unitor and the same actual augmentation definition.

Step 7 is the explicit naturality calculation. The strict Roos comparison is stated natural, so b is natural after the defining realization identifications. The equation is tested after precomposition with kappa^s_kh on a complete object, where step 2 proved invertibility. The reordering of b_h with F^s_h(kappa^s_k) is its naturality at that specific arrow. The identity equation is checked the same way. Fullness of the common categories, stated in the characterization, justifies restriction of the equality. Restoring the identity coefficient transports gives the unsuppressed equations of the item.

I checked empty schemes and the zero object (all displayed maps and triangles specialize), h or k equal to the identity (the normalizations reduce to the identity clause), and E fixed with no coefficient extension (no ramification or finite Tor-amplitude assumption enters). For an incomplete ambient object, steps 1 and the unit normalization remain meaningful, but the final cancellation is not made. An arbitrary automorphism multiplying an endpoint isomorphism would generally change its unit composite and therefore does not satisfy the imposed normalization. This checks that the proof controls the actual compositor rather than only its endpoints.

All cross-unit results are declared as generic tools in split_report.tool_uses: they provide completion, site-equivalence or whole-system calculus; they do not replace the trace-function unit's route. The server preflight accepted the proposed dependency graph, including its cycle checks.

## What could not be finished

Nothing mathematically outstanding. The resumed worker reran the required server dry run before changing this report; it exited successfully with `OK (not pushed)` at commit `77f105c29fe`. The resumed review checked every cited statement, all 20 exact citation quotes, the unchanged item statement and blueprint ancestry, the recorded search results and the relevant upstream Lean definitions. No new node or repeated Mathlib search was needed. A final dry run and direct push follow this report update.
