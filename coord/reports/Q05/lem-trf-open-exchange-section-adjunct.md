## Worker report

Files written:
- dag/nodes/sec-trace-formula/lem-trf-open-exchange-section-adjunct.json: statement split into five explicit steps; statement and statement dependencies unchanged. No new nodes or Mathlib leaves.
- citations.json: one literal quotation for every proof-step dependency.

Attachments: none. Searches of WeilConjectures/ in the read-only slopmaster2 checkout for the exact blueprint tag and open/dual exchange notions found no declaration giving this section-adjoint statement. The derived open-immersion lower-shriek/lower-star exchange found there concerns a different exchange and does not give this normalized ordinary adjunct.

WANTED: none.

The imported item had an empty proof. Its mathematical statement needs no correction. Its normalization hypotheses are essential: an unspecified isomorphism between the displayed functors would not establish the claimed equality of morphisms. The new proof follows the existing inverse-conjugate route, keeping its direction explicit throughout. Varshavsky §0.3(a) and §1.2.2(a)-(b), PDF pp. 5 and 9, supply the adjunction/trace-section/restriction context, but do not print this standalone lemma. The detailed calculation is therefore marked proof_origin.by = agent. No SGA text is used as a source; references in Varshavsky's bibliography are not proof dependencies.

Nothing remains unfinished in this split. The existing dependencies retain their own stage-1 status.

## Existing nodes and Mathlib searches

No new node was needed. I read the statements of the generic adjoint-comparison lemma, the composite-adjunction Mathlib leaf, dual base change and open normalization. Blueprint ancestor search returns lem-trf-local-term-locality, through lem-trf-trace-class-open-restriction. Whole-blueprint searches for exchange, adjunct, adjoint section, open-unit and open inverse-conjugate found the existing generic tools and unrelated Picard section statements, with no second blueprint statement of this item. Searches of the whole DAG found no exact replacement. In particular lem-trf-open-square-exchange supplies restriction of compact-support exchange, but not the ordinary-adjoint conclusion; lem-trf-open-hom-mate concerns the tensor-Hom transpose and is a different statement.

The six searches recorded by msearch.py in searches.jsonl were run for this item and their output read: LeanSearch; Loogle with CategoryTheory.conjugateEquiv and CategoryTheory.Adjunction; two LeanFinder phrasings; and two Mathlib grep patterns. Generic conjugateEquiv/counit tools and ordinary scheme-module restriction adjunctions are not this constructible-six-operation statement. I opened Mathlib/CategoryTheory/Adjunction/Mates.lean lines 270-319: its generic comparison and counit identities support the existing DAG tools; they do not make the whole item a one-line Mathlib specialization, since its normalized sheaf exchange still has to be identified. The inherited item search entries were retained.

## Not duplicates

No new nodes; no new/existing pairs to distinguish.

## Review by Q05

I read Varshavsky §0.3(a) and §1.2.2(a)-(b), the current main-20261015 local-term-locality proof and the dual-base-change proof, and the unit sk-i-curve-zero and chapter sec-trace-formula. This item supplies the open-support restriction of ordinary adjoint sections below the contracting-correspondence reduction; it neither changes that unit's theorem nor substitutes a different route. I also read Stacks categories.tex Tag 0B65, lemma-transformation-between-functors-and-adjoints, and Tag 0DV0, lemma-compose-counits. For the normalization I read sites-cohomology.tex Tag 0GL1, lemma-j-shriek-and-tensor, and sites-modules.tex Tag 0E8I with the same label. Those Stacks lemmas state tensor compatibility, not the whole simultaneous open-unit/base-change normalization; I use exactly the stronger statement of the existing lem-sf-open-tensor-normalization node, which explicitly labels that refinement agent-formulated.

Step 1 uses the actual statements of def-trf-admissibility (specified ordinary/exceptional adjunctions), prop-functor-package (finite-stage smooth purity, specialized to open relative dimension zero), prop-exc-open-adjoint (restriction is the right adjoint of extension by zero on pro-etale derived module categories), and lem-sf-open-tensor-normalization (the inverse exchange is the adjunct of the pulled-back open unit followed by the inverse pullback-composition comparison). The question already requires purity normalized by this open adjunction, so transporting the maps does not choose a fresh right-adjoint isomorphism. For the normalization square the substitution is g=i, j as given, j' the displayed base-changed open immersion, g_U=i_W. The coefficient ring is the same constant finite A on all four sites. The ambient assertion of the normalization theorem restricts to the given constructible domain.

Step 2 uses the hom-bijection statement of def-weil-pbc-composite-adjunction and the ordinary adjunction specified in def-trf-admissibility. I checked all map types: r has source j_!A_W and target A_C; its i-pullback composes with sigma, and its double transpose is precisely Rj^!(v) composed with a after the normalized transport. The elementary equality R(r)u=a is written out by unit naturality and the open triangle identity. Thus the step asserts no unproved Beck-Chevalley identity.

Step 3 uses the inverse-conjugate clause of thm-sf-dual-base-change, with f=j, g=i, f'=j', g'=i_W. This gives the correct direction Rj^!Ri_* to Ri_W*Rj'^!. It uses the displayed counit compatibility of lem-trf-adjoint-mate and the composite hom-bijection of def-weil-pbc-composite-adjunction. I checked the intermediate equation by naturality of b inverse at the morphism beta, then at q; each side has source KQM and target S. The counit identity is part of the cited node's statement, not borrowed from its proof. All functors are the exact functors on the given triangulated constructible categories. Properness is nowhere required.

Step 4 again uses the composite hom-bijection, followed by exactly the inverse-exchange/open-unit assertion quoted from lem-sf-open-tensor-normalization. I checked its orientation: the transpose of b inverse is theta inverse followed after Q(u), giving a map QM to TPJM. Naturality at r then gives the two displayed equalities, and the previous triangle computation removes R(r)u. No unproved comparison between ordinary base change and dual exchange is asserted.

Step 5 is elementary after those computations. The canonical constant-unit and pullback-composition maps take the local coefficient generator 1 to 1; these are maps between the rank-one constant coefficient modules in degree zero. Consequently the remaining comparison identifies the constant unit with itself. Restoring the already specified open-purity identification gives the exact morphism in the question, including its final map into exceptional restriction.

I checked edge cases without adding hypotheses: for the identity open immersion the units and b are identities and the formula is the original ordinary adjunction; for the empty open all target objects and maps lie in the zero category; sigma=0 gives the zero map by each displayed formula. The proof does not assert restriction commutes with arbitrary internal Hom, and does not use geometric-stalk conservativity. This avoids the source's known stalk pitfall. There are no new statements to test on additional small cases. Every proof citation has a literal quote in citations.json. All five steps are below 2000 characters and none hides a separately quantified comparison lemma: the only nontrivial comparisons are the cited existing statements, and the rest are the displayed naturality and triangle calculations.

The generic cross-unit tools are declared in split_report.tool_uses: open purity, the open adjoint, the normalized open exchange, dual exchange, and the adjoint-comparison counit identity. No node of sk-i-curve-zero supplies these generic categorical tools. No maintainer-owned tool_uses or unit metadata was edited.

## Resumed dry-run repair

The required initial dry run rejected two empty quote placeholders for def-trf-admissibility in Steps 1 and 2. I replaced them with literal statement excerpts: the exceptional adjunction with its unit, counit and triangle identities for Step 1, and the ordinary derived module adjunction and its finite-Tor constructible restrictions for Step 2. The earlier local substring check had accepted the empty string, so I corrected that check to require a nonempty quote as well. I reread all cited current statements and the source passages listed above; the saved proof and its statement remain unchanged. No new nodes or searches were needed.
