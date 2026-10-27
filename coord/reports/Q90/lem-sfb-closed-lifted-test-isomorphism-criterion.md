# Q90 stage-1 delivery: lem-sfb-closed-lifted-test-isomorphism-criterion

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-closed-lifted-test-isomorphism-criterion.json: statement, split into eight proof steps; no Mathlib match. The statement and its statement dependencies are unchanged.
- citations.json: one exact statement quotation for every cited node in every proof step.
- report.md: this report.

There are zero new nodes and zero Mathlib leaves. The previous interrupted attempt left only dispatcher marker files; there was no node, report, search log or active delivery to resume. No repository or launcher file was written, no git command was run in the repository, and no Lean/compiler/build tool was run.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint id and for closed lifted tests found no declaration of the item. Broader searches for closed immersions, henselian bases and exchanges found partial results, not this full statement. The already split closed-test derived exchange model is reused as a DAG theorem, not claimed as a closed Lean proof: its own record includes sorries.

## WANTED

None. The needed Stacks sources and the Hemo–Richarz–Scholbach and Bhatt–Scholze papers are available locally.

## What was checked and corrected

The item is unsplit, and no released repair note exists. I read its chapter and unit records, GOAL.md, the worker brief, the three levels in SETUP.md and delivery-errors B–E. The unit's paragraph (3) calls for the closed-base-change input in the open direct-image argument. This item assembles that input without altering the unit route. The blueprint ancestor command returns None, as in the already reviewed exchange-model sibling; I retained the inherited null ancestor and complete via chain, and specified the actual paragraph served. Whole-blueprint searches for the criterion, w-contractible, henselian and exchange found no equivalent statement. Whole-DAG searches by those concepts and Tags 09BK/09BL found existing reusable ingredients.

The source is an agent-extracted criterion, rather than a theorem with this entire statement in one paper. I read proetale.tex Tag 09BK, lemma-closed-immersion-affines, and Tag 09BL, lemma-closed-immersion-affines-apply, including their proofs; HRS Lemma 4.1 and Corollary 4.4 with proofs; the relevant closed-immersion discussion in Bhatt–Scholze §6.1; and sites-cohomology.tex Tag 07A7, remark-base-change. These give the closed-lift and transpose route. The existing derived exchange model supplies the precise derived arrow, slice comparisons and actual coefficient-map compatibility. Its statement does not supply invertibility, which is proved here by detection.

Two semantic searches, a Loogle search, LeanSearch and two source greps were run through msearch.py and their hits read. They return closed-immersion scheme isomorphisms, affine-limit results, generic sheafification isomorphisms, solid/discrete condensed-module predicates, and topological contractibility of normed-module balls. None states this derived internal-module criterion. The sandbox log records those searches as run; the item's earlier search records have been retained. No new node was introduced for a clause of the item, for exactness of evaluating cohomology, or for the few-line cone/separatedness argument.

During writing I corrected a tentative citation to an etale constant-ring Grothendieck theorem: that theorem would not apply to arbitrary internal condensed coefficients on the pro-etale site. Step 6 instead cites the general small-site ring-sheaf Grothendieck theorem, transported by the internal/section-module equivalence. I also checked the Stacks tag-label table: 098F is lemma-w-contractible-proetale-cover and 098H is lemma-w-contractible-is-weakly-contractible. No statement dispute or statement correction is needed.

## Unfinished work

None in the stage-1 split. Existing unsplit dependencies remain existing DAG tasks; this delivery does not claim their Lean proofs are finished.

## Not duplicates

No new nodes. The exact coefficient hypotheses distinguish the item from finite constant-ring exchange theorems, and its global test criterion distinguishes it from lem-sfb-closed-test-derived-exchange-model (which explicitly asserts no invertibility). The henselian quotient and exact evaluation ingredients already exist and are cited directly.

## Review by Q90

I checked each proof step against the actual statements of every node it cites, not its proof. The full statement quotations are in citations.json; the following explains the mathematical uses.

1. The affine closed-site functor theorem states the quotient closed-fibre identification for the specified H_A algebra, and lem-exc-closed-lift-reduction states the specified quotient-ring isomorphism. The henselian-indetale-closed-lift theorem applies to that same colimit algebra. The condensed henselian lisse rigidity theorem states w-contractibility in both directions for any henselian pair. I use only this geometric clause, not its lisse equivalence. This is exactly HRS Corollary 4.4(2); no hidden finite-generation assumption on I is needed.
2. sk-thm-pe-wc-cover gives a faithfully flat ind-etale w-contractible algebra over any ring B. The ind-etale stability theorem explicitly gives composition. The basis theorem explicitly covers every site object by basis objects. This proves that the family in the statement covers, rather than assuming that arbitrary closed lifts preserve w-contractibility without henselianity.
3. The internal/section-module equivalence preserves the underlying section groups. det-pe-wc-sections-exact covers arbitrary ring-sheaf modules; det-pe-wc-sections-derived covers unbounded complexes and termwise evaluation. Exact-functor descent supplies the triangulated functor, and the derived-category definition and distinguished-cone criterion supply the zero/cone test. I wrote the cycle/kernel/cokernel calculation and the sheaf-separatedness argument, so conservativity is proved and is not attributed to the definition of a basis. No spectral-sequence or left-completeness shortcut is needed.
4. The existing derived exchange model has exactly affine f, an arbitrary affine closed immersion, both test schemes w-contractible and bounded-below K. These hypotheses are all verified. It identifies the specified counit mate with the unit-induced restriction, which the item's hypothesis makes invertible. The preceding unbounded detection argument then applies to this very arrow. Nothing is taken from the proof of the model.
5. The square-exchange definition states its actual transpose and naturality. The ringed derived-slice theorem states comparisons for derived inverse/direct images and explicitly says that they preserve units and counits. The derived composition normalization theorem identifies those with composite adjunctions. I wrote the naturality equation before taking its adjunct and checked that square isomorphisms and site restriction leave the same transpose. I do not infer equality of derived arrows merely from equality after evaluating on tests, since those evaluation functors need not be faithful on all derived morphisms.
6. Scalar restriction is exact and unchanged on underlying sheaves by the change-of-scalars statement. The right-derived-functor statement supplies the universal comparison unit and uniqueness. The mate definition fixes the counit equation. The bounded-below derived-mate model explicitly identifies that mate with the right-derived ordinary comparison for exact G,H without requiring preservation of injectives by H. Here G,H are the two scalar restrictions. The general ring-sheaf Grothendieck theorem and internal/section equivalence verify the module categories; the enough-injectives theorem verifies the hypothesis of the bounded-below model. The closed-test model independently states the same comparison for actual coefficient maps. In particular, no flatness or invertibility of scalar direct-image comparisons is being assumed.
7. I checked both transposes of the coefficient square, keeping the directions r Rf_S -> Rf_R r. Substitution of the two counit equations and naturality of theta make them equal. This is a formal calculation from step 6, the mate definition and the scalar-restriction action formula; it is marked elementary. An actual degree-zero map M -> Res N is then inserted by naturality. The tensor unit is an actual such map, even when ordinary extension is not exact.
8. The profinite-test definition makes X[Q] an entire site object, and the slice theorem and adjunction composition theorem apply to its restriction. Repeating the same restriction gives the further-parametrization equations. No pointwise test of Q is substituted for the entire parameter object.

I checked I=0 (identity lift and identity restriction), I=A and the zero ring (empty tests/sites and zero derived categories), empty X, zero modules, zero coefficient rings, arbitrary non-finitely-generated I, nonintegral f and nonlisse K. Degree-zero coefficient inputs satisfy all bounded-below requirements; unbounded joint detection is separate from the bounded-below arrow model. No hypothesis of the latter is dropped. No new statement needs edge-case repair. All eight steps have fewer than 2000 characters, and the longest is one explicit coherence calculation rather than a hidden geometric lemma. All off-unit uses are declared as generic tools in split_report.tool_uses; the constructible-stability unit's route is preserved.
