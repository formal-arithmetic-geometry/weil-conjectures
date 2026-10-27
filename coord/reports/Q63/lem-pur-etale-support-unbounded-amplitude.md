# Q63 stage-1 delivery: lem-pur-etale-support-unbounded-amplitude

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-etale-support-unbounded-amplitude.json: statement retained, six-step proof, status split; no Mathlib match.
- citations.json: one literal statement quotation for every dependency cited in every step.
- report.md: this report. searches.jsonl is the unmodified search-command log. write_split.py is the sandbox-only preparation script.

No new nodes; no Mathlib leaves. No unit/chapter changes, Lean writes, compiler invocations, repository writes, or direct git commands.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and compact-support/amplitude/coproduct notions. Read UpperShriekBoundedBelow.lean, Finiteness/CohomologicalDimension.lean, FiniteCohomologicalDimensionAmplitude.lean, DirectImageAmplitude.lean, and the open-immersion derived-functor documentation. The original-fibre bound in isZero_homology_rightDerivedLowerShriek_singleFunctor_of_two_mul_lt is a heart assertion. exists_isLE_rightDerivedLowerShriekOfCompactification_obj uses a bound from the proper compactification, not every specified bound on f. Neither is an exact attachment giving this item's every clause. Project declarations containing sorry or covering only some clauses were not attached.

## Literature wanted

None.

## Corrections and limitations

The imported statement is unchanged and was not disputed. Its original proof list was empty. The statement's source is Zheng Corollary 2.19; its proof reduces to geometric fibres and exact extension by zero. Here the existing heart-bound node carries that geometric argument, and the additional passage to unbounded-below inputs is written explicitly. Coproduct preservation is obtained independently from the existing ordinary-etale proper-coproduct result before applying a telescope, avoiding circular dependence on the amplitude being proved. No assertion about pro-etale ambient categories is used.

No missing work remains in the split. Dependencies retain their own existing proof status and are not claimed newly proved.

## Searches and duplicate audit

Read the current item and its creator's searches, retaining them. Ran the required msearch leanfinder, loogle, grep and leansearch searches under Q63, followed by a second phrasing about brutal-truncation bounds. All services answered; the actual hits were support predicates, bounded representatives, and etale morphism results, not the item. searches.jsonl records these commands, and the node records precisely their tool/query text and observed hits. No fabricated search or unavailable-as-no-match verdict was added.

Searched all dag/nodes and the whole blueprint via blueprint_refs.py search for compact support amplitude, amplitude, coproduct and fibre-dimension-bound, and searched DAG statements by the individual tools' notions. Reused the existing heart-amplitude, proper-coproduct, geometric-bound, exact-derived-coproduct and telescope nodes instead of creating duplicates. In particular, a new node saying 'unbounded compact-support amplitude' or 'bounded compact-support amplitude' would only rename the desired conclusion or repeat an existing tool.

## Not duplicates

No new nodes, so there are no new/existing node pairs to distinguish.

## Review by Q63

I read GOAL.md, the stage-1 brief, the unit and chapter records, SETUP's three levels, and both copies of delivery-errors B–E. I followed the current main-20261015 exceptional-inverse-image paragraph on finite-level compatible functors; the chapter route is unchanged. The parent exceptional-constant-tensor split confirms that this item supplies its unbounded finite-level support input. I read Zheng's Corollary 2.19 and proof (printed p. 12) and the first paragraph of Proposition 2.23's proof (printed p. 14), not its alternative trace construction. No SGA source is used.

For step 1, I opened the statement of lem-cbc-compactification-geometry-fibre-bound: it gives geometric fibres, not merely ordinary fibres, and allows empty schemes. Apply it over Spec k to X and Y, then over Y to the proper finite-type r and to f. Spec k is Noetherian of dimension zero; proper includes finite type by the cited definition. I read morphisms.tex lemma-finite-type-noetherian (01T6), lemma-morphism-finite-type-bounded-dimension (0A3V), and properties.tex lemma-locally-Noetherian-quasi-separated (01OY). I do not claim 0A3V itself states the geometric refinement: that is the cited geometry node's explicit statement. No separatedness over k is inserted.

For step 2, I read each of the nine cited statements. The module-sheaf Grothendieck theorem and etale K-injective theorem give the categories and resolutions required by the exact-derived and unbounded-right-derived triangulated lemmas. Extension by zero is exact on etale module sheaves, and its cited adjunction is the module-sheaf adjunction, not the abelian-only site lemma. The general left-adjoint theorem gives the sheaf coproducts; lem-pur-exact-derived-coproducts gives their passage to unbounded derived categories. lem-amb-proper-coproducts explicitly gives arbitrary set-indexed coproducts for unbounded ordinary-etale derived categories of finite-ring modules on Noetherian schemes. All of its geometric and coefficient hypotheses hold. I read the exact-functor passage in derived.tex Tag 015F and checked the unbounded source context in the project's derived-functor files. Composition of exact/coprod-preserving functors is an elementary application, not a hidden new lemma.

For step 3, I read the standard-t-structure definition, extension-zero exactness, the bounded-below injective-representative statement and the K-injective total-derived theorem. The representative theorem explicitly allows a cohomological lower bound b and produces injective terms zero below b; it also says bounded-below injectives are K-injective. Hence the unbounded functor is computed by the same complex. No upper bound or convergence hypothesis was used. This is the usual injective-resolution argument of Tags 013K/070J/070K, rather than citing a definition for left t-exactness.

For step 4, I opened lem-dg-compact-support-amplitude and used only its sheaf-level q>2d assertion. A power of ell annihilates C and is invertible on all k-schemes here; there is no assumption that C is a field or regular. The compactification-comparison statement is on D+ of Noetherian schemes, precisely the scope needed for a sheaf in degree zero; the explicit Plus compatibility node identifies bounded-below right derivation with the unbounded functor. I then read lem-pur-bounded-heart-amplitude and apply it with S all module sheaves and [c,d]=[0,2d]. The lower vanishing was already proved in step 3. Its statement gives bounded complexes only, and that is all this step takes. Its Stacks source is the successive-truncation triangle (08J5).

For step 5, the t-structure definition gives a representative E with zero terms above a, and def-kun-truncations explicitly defines lower brutal truncations as subcomplexes. E_n=sigma_{>=a-n}E is therefore an actual increasing sequence of complexes. It is bounded on [a-n,a]; in each fixed degree the transition maps eventually are identities. I checked the statement of lem-kun-complex-colimit-hocolim, which includes module sheaves and no boundedness/monicity requirement, and read derived.tex lemma-colim-hocolim (0949) and lemma-direct-sums (0A5L). The preservation lemma requires exactly an exact functor and countable coproduct preservation, already proved in step 2; it gives an isomorphism relative to chosen telescope triangles, which suffices. No inverse-limit completeness, functorial cones, or incorrect good-truncation direction is asserted.

For step 6, I opened the four cited statements. The module Grothendieck result supplies exact filtered colimits and all sums. Countable sums are filtered colimits of exact finite sums. The exact-derived coproduct statement expressly includes localization preserving coproducts. The exact-colimit homology statement then computes the homology of their termwise representatives; it is not misused as a derived-localization theorem. I read its DegreewiseLimits.lean context. Finally the long-exact-of-triangle statement applies to cohomology; the telescope triangle has H^i(FK) between H^i(B) and H^{i+1}(B), so both vanish for i>a+2d. This proves the upper bound even when K has infinitely many negative cohomology groups.

I tested d=0 (including finite maps), arbitrary shifts a and b (including negative bounds), modules C=Z/ell^s for s>1, a nonseparated finite-type base, zero complexes, and the empty cases. If X is empty, the fixed compactification may have a nonempty boundary, but j_! is still zero; thus d=0 remains valid even then. If Y is empty, every scheme mapping to it is empty. These tests need neither a nonempty fibre nor a regular coefficient ring. The interval conclusion is the intersection of the lower and upper bounds. Every step is under 2000 characters, and no new statement is a restatement or a clause of the item. All generic off-unit uses are listed in split_report.tool_uses for independent review. citations.json quotes were copied verbatim from the current statements, not their proofs.
