## Worker report

Q17, stage 1, 2026-10-21. Item: lem-weil-pbc-flat-constant-tensor-pro-zero-cones.

### Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-flat-constant-tensor-pro-zero-cones.json: existing statement, now split into nine steps. Its statement and statement dependencies are unchanged; proof dependencies are exactly the union of the steps' citations. Earlier Mathlib searches and creation/blueprint metadata are retained.
- citations.json: nineteen entries, one for each step/node citation, quoting the actual cited statements.
- searches.jsonl: five searches run through msearch.py in this session; the item records their actual query texts, returned names and verdicts in addition to its existing searches.
- report.md: this report. write_split.py is sandbox-only preparation material, not a delivery file.

### Attachments

None. Searching lean/WeilConjectures for the item id, its title, and pro-zero/K-flat notions found no project declaration with all the item's hypotheses and conclusions. The homotopy-limit Tower file proves a triangulated statement with a uniform vanishing bound; NormalizedTowerLimit concerns normalized principal-adic towers, not arbitrary strict maps under flat constant extension. Neither is an attachment. I read the existing tensor-cone and cone/quasi-isomorphism declarations supporting their already attached DAG nodes rather than making copies.

### WANTED

None. All sources used are available in the shared read clone.

### What needed repair or explanation

The imported item was statement-only. Its reference to Stacks 099M is an extraction of the transport argument implicit in that lemma, not a verbatim theorem there. I read proetale.tex, lemma-naive-completion: it passes from the Koszul pro-system to the quotient pro-system after derived tensor. The present split spells out the general functorial transport and the strict-unit normalization. It is marked proof_origin.by = agent because this full general statement and its explicit normalization are written here, with its ingredients sourced individually. There is no statement dispute, source correction, added hypothesis, or route change.

In particular, lem-weil-pbc-kflat-fixed-tensor-triangulated is not used: its statement requires flat terms in the fixed K-flat complex. The present item has no such hypothesis. Step 3 instead uses the definition of K-flatness and the existing general cone comparison; this avoids incorrectly importing that extra assumption. No termwise flatness or boundedness of P is inferred from K-flatness.

### Unfinished work

None for this one-level stage-1 split. Existing dependencies remain the existing DAG's responsibility; no Lean was written and no compiler, Lake, or build was run.

## Blueprint and searches

I read GOAL.md, the three levels in SETUP.md, the chapter sec-proper-base-change and unit sk-thm-properbasechange, and the current main-20261015 completed-pullback definition at sec-proper-base-change/sk-prop-pbc-complete/def-weil-pbc-completed-pullback.md (order 1329). The ancestor is def-weil-pbc-completed-pullback through lem-weil-pbc-constant-completion-equivalence. The latter's Step 7 invokes exactly this transport for constant and completed coefficients; this split supports the ancestor's final equality and the assertion that the comparison is the completion map. The item already had a precise from.place, which is retained. No unit/chapter fields were edited.

Whole-DAG title/statement searches for exact constant sheafification, tensor cones, K-flat quasi-isomorphisms, localization, and pro-zero towers found the existing nodes used below. I opened each of their statements. blueprint_refs.py searches for 'pro-zero', 'constant exact', 'tensor mapping cone', 'K-flat', 'constant module sheafification', 'flat constant', and 'pro-zero cone' found no blueprint theorem equivalent to this item. In particular the completed-pullback definition is a consumer, and the finite-coefficient flat inverse-image node is a different assertion. same_as remains empty. The existing cone and exactness nodes made new nodes unnecessary.

The five fresh item searches are the leanfinder query beginning 'A flat constant sheaf extension', leansearch query beginning 'An exact functor on complexes', loogle pattern '"KFlat", "quasiIso"', grep pattern 'pro.?zero|proZero|KFlat|K.flat' in CategoryTheory, and a second leanfinder phrasing beginning 'Functorial derived inverse limits'. The first semantic search returned mapDerivedCategoryFactors and additive-functor mapping-cone comparisons. These supply only ingredients; exact-functor descent already has a Mathlib-leaf node. LeanSearch returned exactFunctor, exact_tfae, and tensor exactness for ordinary flat modules. The second phrasing returned ordinary ModuleCat flat scalar-extension exactness, not a ringed-site strict-tower result. Loogle had zero hits. The grep hits were prodZero/coproduct zero-object declarations, false positives for the pro-zero pattern, not tower lemmas. No hit gives the full item or a one-line specialization of it. The five log records, including the second phrasing's returned names, were read before recording these verdicts. No unavailable search was called a negative result.

## New nodes

None. New Mathlib leaves: zero.

## Not duplicates

No new nodes exist, so there are no new/existing node pairs to distinguish.

## Review by Q17

I reviewed delivery-errors.md B through E against the statements and the sources, including the potential mismatch between K-flatness and flat terms. The item is self-contained on its small site, Noetherian coefficient ring, constant ring sheaf, flat coefficient map, strict towers, and arbitrary K-flat complex. Noetherianity is retained although this transport argument does not need it; it is used by the parent's Koszul pro-comparison. The statement already defines pro-zero explicitly. All nine steps are under 2000 characters; none hides a separately needed comparison lemma.

1. I opened lem-weil-pbc-finite-type-constant-exact: despite its id, its statement is for every module over every commutative ring, with no finite-type restriction. I also read its existing Sheaf.CategoryTheory.FiniteTypeConstantExact source. Stacks sites-modules.tex lemma-constant-exact (093J) gives the exactness used. def-pc-flat-sheaf-modules says exactly that fixed tensor is exact, as verified in definition-flat (03ER)(3)-(4). This is sufficient here, rather than a weaker flatness criterion. lem-weil-pbc-module-sheaves-colimits-forgetful states faithfulness and preservation of kernels/cokernels; Step 1 uses precisely these to pass from underlying R-modules to O-modules, and writes out why zero homology is detected. Smallness supplies sheafification. No assumption on exact products is involved.

2. I read lem-weil-pbc-exact-functor-derived-factorization, an existing Mathlib leaf. It gives unbounded quasi-isomorphism preservation and the natural termwise/localization comparison required here. I checked its source derived.tex lemma-right-derived-exact-functor (015F). Step 2 uses exactness established in Step 1; it does not derive an unbounded functor from bounded-below resolutions. Preservation of zero morphisms is the elementary factorization through the zero object, explicitly stated.

3. I checked def-pc-tensor-complex-sheaves for direct-sum totalization and its signs; def-pc-kflat-complex for testing all acyclic complexes; lem-pur-quasi-iso-cone-acyclic for both directions of the cone criterion; and lem-pc-tensor-mapping-cone-iso for tensor by an arbitrary fixed complex on a site. These are the actual statements used, not their proofs. I read sites-cohomology.tex definitions/lemmas 06YM, 06YN, 06YP and the existing project cone declarations. The signed interchange is written with both parity identities, so the acyclicity assertion uses the definition's right tensor factor correctly. This step never substitutes the one-point-site K-flat quasi-isomorphism lemma for a ringed-site lemma, and it never assumes the varying complexes are K-flat.

4. lem-weil-pbc-localization-universal-property explicitly supplies the descended functor and its natural comparison for a functor inverting the quasi-isomorphisms. def-weil-abstract-derived-category states that this localization is the unbounded derived category of complexes. Step 3 supplies the precise inversion hypothesis. T(0)=0 and factorization through zero prove preservation of zero maps; no additive descent theorem is silently required.

5. I checked the cone matrix in def-weil-abstract-derived-category against derived.tex definition-cone (014E), and the strict-square map against lemma-functorial-cone (014F). Finite biproduct preservation by additive E gives the first comparison in two matrix lines. The second comparison is exactly the natural isomorphism asserted by lem-pc-tensor-mapping-cone-iso. Its statement has arbitrary unbounded fixed complex and naturality, so it applies to all tower transition squares. There is no unjustified choice of unrelated derived cone maps.

6. This step is elementary from the already established natural functor comparisons and cone isomorphisms. It chooses the original m for each n and conjugates the image transition by the two theta maps. It does not identify a zero derived morphism with a zero chain map, nor require a uniform m-n. The m=n case is explicitly included.

7. I opened the entire statement of lem-weil-pbc-ringed-strict-tower-homotopy-limit, not just its definition of a homotopy limit. Its last clauses give both the pro-zero consequence and the canonical Rlim(v) isomorphism for a strict map. This is exactly what is used. I read sites-cohomology.tex section-derived-limits (0940) and lemma-derived-limit-is-ok (0941), including the tower-site interpretation and K-injective computation. The input is a strict tower on a small site; products may fail to be exact and no bound is imposed. The needed theorem is already in this unit, so no new Rlim lemma is introduced.

8. The unit identification is degreewise the tensor multiplication and p to p tensor 1 from the cited definitions; this is elementary. Strict commutation of the original unit maps yields w alpha = beta before localization. The cited ringed-strict-tower statement explicitly computes Rlim by a tower K-injective resolution and termwise limit, so the two specified maps are exactly the limit factorizations in the step. There is no assertion that arbitrary maps into triangulated homotopy limits are unique.

9. I checked lem-weil-pbc-kinjective-hom-derived and its source derived.tex lemma-K-injective (070I). It applies to any abelian category, hence to the strict tower category used in the cited Rlim theorem, not only levelwise module complexes. Its surjectivity supplies h, and its injectivity supplies a tower homotopy after precomposition with j_Z. The step writes the homotopy equation and applies the additive inverse-limit functor, proving equality after localization. The same Rlim computation identifies lim h with the canonical Rlim(w), so the unit compatibility concerns the particular isomorphism of Step 7. This also makes the conclusion independent of the resolution choices.

The generic cone criterion and tensor-cone comparison are already Lean-closed nodes, so they are tools allowed from their units. The other cited statements lie in this unit, in the reduction unit explicitly cited by it, or in its exchange route; exact-functor descent is a Mathlib leaf. No new tool_uses authorization or route substitution is requested. I checked the dependency paths of the existing substantive lemmas: none reaches this item, so none creates a cycle.

For small cases I checked P=0, identity v, zero original cones, a zero ring or degenerate sheaf category, and a tower with zero transition maps but nonzero individual terms. The proof still sends the same zero transitions to zero and uses the genuine derived-limit theorem, not termwise acyclicity or a limit of sections. For nonuniform pro-zero towers the chosen m remains dependent on n throughout. Arbitrarily unbounded direct sums are used only in total tensor; no interchange of tensor with countable products or inverse limit is claimed. The flat-extension and K-flatness hypotheses are used in Steps 1 and 3 respectively, and the strictness/unit hypothesis first enters Step 8. There are no new statements to test separately.

## Second reading by Q17

This is the self-review and direct-delivery workflow authorized in the brief, not a claim of an independent second worker. On rereading the actual statements I rejected the tempting fixed-tensor triangulated lemma because of its flat-term hypothesis, retained the cone-based proof for general P, and checked the tower-level Hom comparison in the unit argument. I also checked that no statement or dependency has been weakened to obtain the result, that the quoted text in citations.json comes from each cited statement, and that all steps have explicit elementary judgments and individual source places. The server dry run via deliver.py --no-push exited successfully: preflight passed at f07a16572a7. This checked the item, its citations and the DAG without any local Lean compilation. The final report records that successful check; the unchanged mathematical split is validated once more before the direct push.
