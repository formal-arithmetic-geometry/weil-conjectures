# Q98 worker report

## Files written

- dag/nodes/sec-smooth-purity/lem-sf-exact-pullback-tower-counit-comparison.json: split the item in four proof steps. Statement, statement dependencies, provenance and creation metadata retained. Existing Mathlib searches retained and five actual searches appended. No new nodes or Mathlib leaves.
- citations.json: ten entries, one for every cited node in every proof step, each quoting that node's entire statement verbatim.
- report.md: this report and signed mathematical review.

## Attachments

None. Searching the exact blueprint tag in lean/WeilConjectures gives no declaration. Concept searches for tower counits and exact tower pullback find CyclePullbackCore.lean and Compactification/Tower.lean, concerning cycle pullback and compactifications rather than these module-derived comparisons. Related derived-pullback composition counit declarations concern compositions of scheme morphisms. The broader parent normalization declaration in lean/Sheaf/Paper/SfExactPullbackCounitNormalization.lean is sorried and is not an attachment. No compiler or Lake command was run.

## WANTED

None.

## What changed and sources

The item was unsplit with no repair-note file and no previous sandbox item or report. It arose by distributing the normalization parent's old Steps 1--3; those arguments are preserved in coord/reports/Q80/lem-sf-exact-pullback-counit-normalization.md and were read. I read the current main-20261015 blueprint localization statement, the chapter and unit records, the stage-1 contract, GOAL.md, SETUP's three levels and both B--E delivery-error sections. The current blueprint statement has no detailed normalization proof. This proof is marked agent-written, with explicit supporting sources, and keeps the same normalization route. No statement dispute or hypothesis change was needed.

I read Stacks derived.tex Tag 015F, lemma-right-derived-exact-functor, including the unbounded clause and proof, and Tag 06XN, lemma-find-existence-computes, including both resolving hypotheses and its left-derived dual. The exact-descent and normalized evaluation DAG statements supply the precise universal and normalized forms used here; I do not attribute the simultaneous comparison identity verbatim to Stacks. Localization of natural transformations uses the existing Mathlib-backed localization universal-property node. I read Mathlib/CategoryTheory/Functor/KanExtension/Basic.lean lines 100--158, including the counit-normalized right Kan isomorphism at 134--145, Algebra/Homology/DerivedCategory/ExactFunctor.lean lines 24--65, including mapDerivedCategoryFactors at 41, and Functor/Derived/LeftDerived.lean lines 182--208, including totalLeftDerivedCounit at 198. No SGA source was used.

## Searches and existing nodes

I searched the whole DAG by the two Stacks labels/tags and by exact-functor, evaluation/localization and K-flat comparison concepts; whole-blueprint searches used blueprint_refs.py search 'exact functor', 'evaluation', and 'counit'. The ancestor command returns prop-sf-localization-all-stages. The existing blueprint provenance already has a precise place and same_as=[], which are retained. Full statements of all seven distinct cited nodes were opened, along with the K-flat left-derived criterion and abstract derived-category definition. A traversal of each proposed principal tool's statement and proof dependencies found no dependency back to this item.

Five searches for the item ran through the required msearch.py: LeanFinder twice with different phrasings, Loogle for CategoryTheory.Functor.totalLeftDerivedCounit, LeanSearch for exact universal derived counits commuting with tower evaluations, and grep for rightKanExtensionUnique|mapDerivedCategoryFactors|totalLeftDerivedCounit. Every service returned available and its actual hits were read. The searches are recorded with their literal queries from searches.jsonl. The hits provide the generic exact localization and universal-counit ingredients, already represented in the DAG, and degree-zero derived results requiring projective resolutions. No hit states the simultaneous ordinary/tower comparison with normalized evaluation and transitions. The historical item searches remain historical records, not claims that I ran them. No new node requires searches or same-tag duplicate comparisons.

## Review by Q98

Step 1 cites lem-weil-pbc-exact-functor-derived-functor, whose clause (1) explicitly says (F_D,xi) is the left-derived/right-Kan pair on the unbounded derived category. It does not merely assert a termwise representative. The specified pair (L,epsilon) is universal by the item's hypothesis. The written inverse-composition argument transfers that property through Q(m), without appealing to an unstated transport theorem. The second citation, lem-sfb-right-kan-extension-unique-iso, explicitly supplies the unique isomorphism with eta (uQ)=epsilon, including its inverse. Taking eta=xi gives exactly the displayed equation with the correct direction. Solving it for epsilon establishes invertibility on every complex, not just K-flat ones.

Step 2 cites the levelwise-abelian tower statement for its exact evaluations and its explicit kernel/cokernel formulas. These make levelwise F additive and exact and make its source and target abelian, so the exact-derived theorem and Kan uniqueness apply to the entire strict tower category. Naturality of m at each transition supplies a strict tower map. The construction uses the specified tau; it does not replace the chosen universal pair by an unrelated model. Solving the Xi equation makes every tau_M invertible. This is the same proof as Step 1 with the hypotheses checked, not a new clause restated as a node.

Step 3 uses exact evaluations from levelwise abelianness, exact termwise descent from lem-weil-pbc-exact-functor-derived-factorization, and the natural-transformation lifting and identity/composition clauses (2)--(3) of lem-weil-pbc-localization-universal-property. The functor M -> Q_S F(M_n) inverts quasi-isomorphisms because evaluation is exact and F is exact. Its two factorizations therefore have a unique identity-induced interchange h_n; lifting the inverse identity proves it invertible. The equation xi h_n=ev_n Xi fixes its direction. Defining w=e^{-1} h_n ev_n(E) is then an elementary composition of natural isomorphisms. No assertion about equality of tower morphisms is inferred just from their evaluated components.

Step 4 uses precisely the same small ringed sites and coefficient map as the normalized tower-evaluation statement, with its F instantiated by our G. The diagram-replacement statement supplies simultaneous strict objectwise K-flat flat-term representatives for the small index category of positive integers with reversed order; its pullback quasi-isomorphism clause verifies the resolving hypothesis. The evaluation theorem states both uniqueness with epsilon v=ev(tau) on this class and the exact transition equation for every derived strict tower. The displayed calculation first proves that the constructed w satisfies that normalization (indeed on every complex, since Step 1 established invertible epsilon). Hence uniqueness identifies w with v, and the stated comparison equation follows by multiplying by e. The existing theorem supplies every b>=a transition, including identity transitions, without a hidden compatibility argument or a new lemma duplicating a clause.

The proof has no step longer than 2000 characters. I checked B--E against the files: statement dependencies remain appropriate, every non-elementary fact comes from an opened cited statement, citation quotes are literal, the union of uses is proof_deps, no new nodes restate clauses or elementary consequences, and no proof source or parent is introduced as a circular dependency. The only non-Mathlib off-unit tools are declared in split_report.tool_uses with their generic roles. No maintainer approval fields were written.

Small cases: for F=G and m the identity, the comparisons are the unique maps fixed by the prescribed counits, rather than an unjustified claim of literal identity between independently chosen functors. Twisting m by a natural automorphism twists e and E together and cancels in e^{-1} ev(E), as the calculation requires. The zero complex and zero tower give the unique zero-object maps; a tower with noninvertible or zero transition arrows still works because only naturality at those arrows is used. The case b=a is the identity equation. A genuinely unbounded complex needs neither a truncation nor a bounded resolution: exact descent is unbounded, and the simultaneous diagram-replacement theorem is unbounded. Small sites and the fixed small tower index meet the cited size hypotheses. No completeness, flatness of arbitrary input M, or injective-component hypothesis is added.

## Not duplicates

No new nodes were created. Existing exact descent, Kan uniqueness, strict diagram resolutions and normalized evaluation are cited instead of recreated.

## Unfinished work

No mathematical split obligation remains. This delivery is stage 1 only and makes no claim of a formal Lean proof. Server validation and delivery are performed with the required tools.
