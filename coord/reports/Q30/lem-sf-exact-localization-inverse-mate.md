# Stage-1 report: lem-sf-exact-localization-inverse-mate

## Files written

- dag/nodes/sec-six-functors/lem-sf-exact-localization-inverse-mate.json: statement, split into six steps; no exact whole-item Mathlib match.
- citations.json: verbatim cited-statement excerpts for every step/node pair.
- report.md: this report. searches.jsonl contains the actual search-command results.

No new nodes and no new Mathlib leaves. The existing exact-functor factorization and localization universal-property leaves supply all general localization facts needed here.

## Attachments

None. I searched the project source under lean/WeilConjectures by the blueprint tag, inverse-mate terminology and localization/derived-mate terminology. The helpers exact_hom_fac and exact_inverse_mate_isIso are private declarations in lean/Sheaf/SixFunctors/SemilinearProperOpenMatePasting.lean:2006 and :2036, not an eligible exact attachment in WeilConjectures. The project theorem exactMateComparison_eq in WeilConjectures/CategoryTheory/DerivedExactMateCompatibility.lean has K-injective and right-derived comparison hypotheses absent from this item, and does not assert its Hom clause. I did not treat these as attachments.

## WANTED

None. The available sources suffice. The general exact-localization mate calculation is supplied by the author, rather than attributed to a theorem that only constructs geometric base change.

## Corrections and route

No statement correction and no statement dispute. The imported node had no proof. Its source's Stacks 07A7 (sites-cohomology.tex, remark-base-change) specifies the adjunction convention and constructs geometric base change; it does not itself prove this abstract normalization. I read its full construction, and read Stacks 015F (derived.tex, lemma-right-derived-exact-functor) for exact termwise derivation. The latter's omitted details are supplied here by the existing exact-functor factorization Mathlib leaf, not silently assumed.

I read the current blueprint fix-prop-coherence.proof.md, especially its units/counits and preservation-of-mates sentences, and the chapter and sk-thm-sf-compatibility unit records. The argument follows that route: preserve the original unit and counit, then expand their mate. Nothing about purity, compactification or another geometric route enters the proof.

## Not duplicates

No new-node/existing-node pairs: no new nodes were created. Whole-DAG and blueprint searches by localization, localization adjunction and inverse mate were read. The existing lem-sc-localization-nested-adjunction-mate concerns a special nested mate and arbitrary derived left-adjoint presentations; it does not include this general six-functor square with the specified Hom normalization. lem-pod-derived-exact-square-composition concerns composition of exact squares, not mates. Both were left untouched. The two genuinely generic tools already have nodes, so neither was duplicated.

## Review by Q30

I checked B through E of delivery-errors.md against the completed node and the sources, including both copies of those sections. There are no statement-only new nodes to audit, no tags used in place of proof dependencies, and no clauses moved into replacement nodes. Every object was already introduced in the item's statement; its original statement, source, chapter, unit, created record and blueprint ancestry are retained. The original search records are retained, and the five actual searches in this attempt are appended with their exact tool/query text and observed results. Both natural-language phrasings returned only general localization/derived adjunction ingredients. I read Mathlib's Localization/Adjunction.lean, the universal-property API in Localization/Predicate.lean and the exact-functor factorization source before deciding that these do not constitute a whole-item one-line specialization.

For step 1 I opened lem-weil-pbc-exact-functor-derived-factorization: it explicitly gives preservation of quasi-isomorphisms and the natural factorization phi for every complex, with no boundedness or K-injective assumptions. I opened lem-weil-pbc-localization-universal-property: clause (2) explicitly lifts transformations, gives the component formula, and preserves compositions and identities, while clause (3) detects equality after precomposition. These say exactly what the step takes. The composition factorization chi is the displayed composite of two phi maps; its use requires no separate composition theorem.

Step 2 uses def-weil-exact-derived-adjunction for the specified degreewise cochain adjunction. I wrote both Hom formulas and the degreewise naturality/triangle argument, so this step does not smuggle in the existence of unrelated derived adjoints. Additivity is enough for degreewise cochain constructions; exactness is available for the later localizations.

Step 3 uses that same definition's explicit sentence that units and counits are localized original ones, the transformation component formula of the universal-property leaf, and the natural factorization isomorphism of the exact-functor leaf. I checked the types: chi(R,L,K) has source D(R)D(L)QK and target Q(R#L#K), so its inverse follows Q(eta_K). The counit uses chi(L,R,N) in the opposite position. The two cancelling D(R)(phi_L) maps and the naturality identity at f are written out. Thus the conclusion concerns the specified adjunction's actual Hom bijection. No alternative adjunction is substituted.

Step 4 uses the full inverse formula in def-weil-pbc-adjunction-mate, which I opened. Its d goes from GR1 to R2H, and its inverse mate goes from L2G to HL1. The formula needs d itself, not d inverse. Componentwise equality of complexes is literal equality in each degree, and naturality ensures the maps commute with differentials.

Step 5 uses that same inverse formula, the localized unit/counit sentence, and the two localization leaves already read. I checked each of the three arrows under the iterated factorization maps: the first is localized L2#G#eta1, the middle is localized L2#d at L1#K after naturality moves the argument along phi_L1, and the last is localized epsilon2 at H#L1#K after naturality moves along chi(H,L1). These are exactly the three maps of step 4. Endpoint comparisons are chi(L2,G) and chi(H,L1), with the latter inverted. This is one routine expansion of the defining three-arrow composite, not a separate comparison lemma left unstated. All six steps are shorter than 2000 characters.

Step 6 uses precisely clauses (2) and (3) of the universal-property leaf. Equality is extended as equality of natural transformations by precomposition with Q; it is not deduced from faithfulness of Q on individual morphisms. The inverse comes from lifting beta inverse and its two actual inverse identities. Invertibility of d alone would not suffice; the explicit hypothesis that beta is invertible is used here. No essential-surjectivity theorem or roofs argument is being silently invoked.

I tested the statement and formulas for zero categories, zero complexes, identity functors with the identity square, and a nontrivial scalar automorphism of the identity adjunction: the mate and its localization have the same scalar, rather than its inverse. Nontrivial units for a non-identity adjunction are retained in step 3, so there is no assumption that every unit or counit is invertible. All functors are exact as required, all localizations and Hom sizes are chosen as stipulated, and no smallness, boundedness, enough-injectives or K-injective hypothesis is introduced. Every cited node statement was opened and every citations.json quote is copied verbatim from it.

## Unfinished work

None in the one-level split. No Lean file was written and no compiler, Lake or build command was run.
