# Stage-1 dedicated repair: lem-cbc-initial-prism-horn-filtration

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-initial-prism-horn-filtration.json`: split, five short steps; statement and Lean record unchanged.
- `dag/nodes/sec-smooth-purity/lem-cbc-nonfree-chain-completions.json`: new statement-only finite-poset lemma, unsplit; no exact Mathlib match.
- `citations.json`: verbatim statement excerpts for every step's citations.

One new node; zero Mathlib leaves. The previous NP report is retained as `prior-report-NP.md` in the sandbox. Its removed general pushout helper remains removed. All inherited searches and review records remain in the item; the NU search log records the actual searches for the new child.

## Attachments

None. Read-only searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the blueprint tag, initial prism/horn filtration and `exists_initial_prism`, and in the exact master reference, found no finished declaration stating the item. The inherited stage-2 `SSet.exists_initial_prism_horn_filtration` record is a statement with a postponed proof; it is preserved, not used as finished evidence. Searches for the child's chain-completion concept likewise found no attachment.

## WANTED:

WANTED: archival Kerodon Lemma 4.4.4.7, tag 01DN, for the item and `lem-cbc-nonfree-chain-completions`. I read the entire online statement and proof at https://kerodon.net/tag/01DN on 2026-10-17. This is a Kerodon tag, not a Stacks tag. No download or literature edit was made. The inherited agent proof-origin record remains applicable. No SGA source is used.

## What was wrong; repair of the return

The dedicated handoff in `coord/returns/NU.md` asks for the hidden arguments of former step 3 (2486 characters) to become cited nodes, preserving the statement, route, other steps and Lean record. The hidden classification was the assertion that the missing face has only two possible free one-vertex enlargements. I extracted that assertion as `lem-cbc-nonfree-chain-completions`, formulated for arbitrary strict chains in the finite coordinatewise product, without any filtration or pushout conclusion. This is a proper sublemma, not an item clause or a renaming of the full horn-intersection argument.

The included-face computation stays as step 3. Step 4 checks the missing face satisfies the new lemma's hypotheses, cites its explicit two-completion conclusion and compares their indices with the enumeration. It then concludes the horn inverse-image equality from the horn definition. The original final gluing step is step 5; only its reference to the preceding step number changed. Steps 1 and 2 are byte-for-byte preserved, as is the included-face part of step 3. The item statement, statement dependencies, source, blueprint ancestry, Lean record and all historical audit fields are unchanged. The proof dependencies gain exactly the new child. All non-elementary steps are now below 2000 characters: lengths 1482, 978, 983, 1188, and the elementary final step 1092. This is an extraction, not just paragraph splitting.

## New nodes

`lem-cbc-nonfree-chain-completions` is an unsplit statement with no proof or proof dependencies. It defines its finite ordered product, strict chains and free chains inline, and introduces all parameters. It assumes n>=1, both required coordinate-coverage conditions and absence of a vertical pair. Its conclusion explicitly handles p=0 and classifies the inserted vertices, with zero-based positions. The finite ordered sets cite def-weil-pbc-simplicial-set, whose opening sentence defines exactly these ordinals; strict product chains and free chains are defined inline. Its chapter/unit are inherited; its blueprint ancestor and via-chain include the item, and its exact source place is the missing-face argument of Kerodon 01DN. No same-statement blueprint node was found.

For the future split, the argument intended by the source is as follows (this explanation is in the report, not in the unsplit statement). Every coordinate below p must precede the first (p,1) with second coordinate zero; (p,0) is absent since otherwise there is already a vertical pair. Thus the prefix is forced. Creating a vertical pair by a single insertion requires adding one endpoint to an endpoint already present. Inserting (b,0) before a later (b,1) is blocked by the earlier (p,1), unless b=p. Inserting (b,1) after a zero vertex is blocked by the next (b+1,0) unless b=p-1. These are exactly the two asserted insertions; the second exists only for p>0. Both retain all required coordinates and acquire second coordinate zero, and their vertical pairs have the asserted positions. This classification is the non-elementary subclaim formerly proved inline.

## Not duplicates

lem-cbc-nonfree-chain-completions vs lem-cbc-initial-prism-horn-filtration: the child classifies one-vertex completions of arbitrary finite product chains; the item constructs an ordered simplicial filtration with pushouts and endpoints.

lem-cbc-nonfree-chain-completions vs lem-cbc-invertible-prism-extension: the parent extends maps into a quasicategory for arbitrary simplicial inclusions; it does not state this finite-poset classification.

lem-cbc-nonfree-chain-completions vs prop-pur-weil-equivariance-scheme-frobenius: this other whole-DAG 01DN text hit concerns precomposition of scheme-Frobenius squares, not a product-chain lemma; the tag collision supplies no mathematical overlap.

lem-cbc-nonfree-chain-completions vs lem-coef-infinity-right-prism-boundary: that node gives an interval/right-horn filtration, not a classification of all one-vertex completions of arbitrary nonfree chains.

lem-cbc-nonfree-chain-completions vs lem-coef-labelled-spine-prism-horn-calculus: that node concerns labelled inner horns and Segal spines, not the possible completions with adjacent initial vertical indices.

lem-cbc-nonfree-chain-completions vs lem-weil-pbc-simplicial-set-glue-simplex: that node proves a full-boundary simplicial pushout under degree conditions, not the classification here.

I searched the whole DAG by 01DN, vertical pair and chain-completion vocabulary, and used `tools/blueprint_refs.py search` for prism, horn, free simplex, 01DN and chain completion, across the whole imported blueprint. The current main-20261015 compact-support proof opens with the same compactification choice; the inherited ancestry is retained. No new unit or route is introduced.

## Review by NU

I read delivery-errors B–E completely, the item and all three cited definition statements, the sec-smooth-purity chapter and sk-prop-sf-cbc unit, the current main-20261015 proof of thm-cbc-finite-level-proetale, the parent invertible-prism statement, the earlier NP report and the dedicated NU return. I compared every clause of the item with the online Kerodon 01DN statement: m>=0, n>=2, the initial union, finite sequence, q>=2, p<q, each pushout, and the p=0 endpoints agree. The new child's finite-poset formulation isolates the final paragraph of that proof and its nonfree-chain prefix from the exhaustion paragraph; it does not strengthen the filtration statement or add hypotheses to it.

Step 1 cites def-cbc-enhanced-diagrams-cones for weak-map standard simplices and degreewise products, and def-weil-pbc-simplicial-set for degeneracy, operators and subsets. The proof explicitly checks degeneracy by repeated pairs, finiteness by bounded-length strict chains and the enumeration; no general nondegenerate decomposition theorem is assumed. Step 2 uses the horn definition in enhanced-diagrams-cones: omission of a positive second coordinate puts the chain in the zeroth horn. Coverage of every first coordinate forces the zero prefix; insertion covers the remaining chain, including p=0.

Step 3 uses that same definition, and keeps the three explicit deleted-face cases. For a<p the omitted first coordinate puts the face in the boundary; for a=p+1 a later vertex exists because n>=2, and either 1 is lost or inserting (p+1,0) gives an earlier equal-dimensional free simplex; for a>p+1 failure of coverage puts it in X0 and otherwise its smaller dimension places it earlier. These are direct computations with the constructed chain, not an unexplained appeal to a general face theorem.

Step 4 cites the new child for exactly the list of free one-vertex completions. Its hypotheses hold: deleting (p,0) retains first coordinate p through (p,1), retains every positive second coordinate, and destroys the unique zero-to-one vertical pair. An earlier containing free simplex must be exactly one dimension larger, because the chain is nonfree and the enumeration is dimension ordered. The returned completion either is sigma_s itself or has smaller index and so is later. The p=0 case has no second completion. Enhanced-diagrams-cones supplies the exact horn-as-omitted-vertex definition for the concluding inverse-image equality; the chain/repetition analysis already established in step 1 covers degenerate simplices. No proof of the child is used, only its complete statement.

Step 5 uses def-weil-pbc-simplicial-set for natural transformations and def-weil-pbc-category-colimit for unique cocone factorization. I checked that the attaching simplex is embedded degreewise. Maps on the two simplicial subsets glue uniquely and naturally because their intersection is the horn image; the indexing span is finite and therefore small. This argument is elementary, with no missing general pushout theorem. Surjectivity of the second coordinate gives q>=n>=2, the vertical pair yields p<q, and its positions prove the stated endpoints. Exact relevant excerpts from all cited statements are in citations.json.

For B1–B9 and C1–C5, the child has only a statement, no proof sketch, no hollow definitions, no borrowed undefined objects and no invented Stacks attribution. All searches were actually run through msearch.py. Two distinct semantic phrasings, Loogle, LeanSearch and two greps found related Mathlib facts, but no match. I read UnionProd.lean:87–110,124–209,250–320: uniqueness of an index within a fixed simplex and reconstruction of its paired face do not classify all possible superchains. I also read IsUniquelyCodimOneFace.lean:64–104 and PairingCore.lean:175–215; their uniqueness concerns a face operator for an already fixed pair. The general LTSeries refinement and Profinite Boolean-product hits likewise do not give the two explicit extensions. The actual query strings and results are recorded unchanged. A Mathlib leaf would therefore be unjustified.

For E1–E5, I checked the child at n=1 as well as the item's n>=2, at m=0, p=0 and p=m, and with arbitrary later repeated first coordinates in strict product chains. The sandbox check_chains.py exhaustively enumerates all strict chains for 0<=m<=3, 1<=n<=4 with (m+1)(n+1)<=16 and tests the exact two-completion assertion. All 15 parameter pairs passed, covering 152 qualifying chains, with counts 1,1,1,1; 2,4,6,8; 3,9,19,33; 4,16,44 by increasing m,n. This checks the generalization to n=1 and the absence of a fictitious p=-1 completion. The proof itself remains the cited source argument, not a finite-check inference. No coefficient hypotheses, statement dispute, circular dependency or SGA route occurs.

What changed on self-review: I found and read the dedicated return instead of treating this as an unsplit blank item; retained the former proof and review, extracted the actual completion-classification subclaim, and made the missing-face step cite it. No unrelated file is delivered.

## Unfinished work

None for this one-level repair. The new child intentionally joins the stage-1 queue as an unsplit statement. No Lean was written or compiled. The source archive remains WANTED.

## Validation repair

The first completed server preflight requested a cited definition in the new statement. I added the existing def-weil-pbc-simplicial-set for its finite totally ordered sets, and added that exact statement dependency. Its opening sentence defines [r]={0<...<r}; no theorem or undefined product-order convention is imported. The new lemma is otherwise unchanged, and the item statement and Lean record remain untouched. The preliminary dry run before this repair had rejected the historical NP report for lacking the NU signature; the report was rewritten with the complete NU review above.
