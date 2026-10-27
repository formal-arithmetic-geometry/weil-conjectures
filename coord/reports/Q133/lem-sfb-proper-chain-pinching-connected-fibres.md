# Stage-1 delivery: lem-sfb-proper-chain-pinching-connected-fibres

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-proper-chain-pinching-connected-fibres.json: statement, split; no exact Mathlib match. Six proof steps, thirteen existing proof dependencies.
- citations.json: one verbatim statement quotation for each of the 23 step citations.
- report.md: this report. No new nodes and no new Mathlib leaves.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint id and by pinching, chain and geometrically-connected terminology found no declaration giving this item. General connectedness and Stein-factorization declarations are not the pinching theorem.

## WANTED

None for this item. Its geometric and topological inputs are already available in the repository.

## Corrections and scope

The statement is retained exactly. Its source calls this an agent consequence of 0E25; that tag does not itself assert the connectedness theorem. I read its proof and used only the cartesian/conductor relation already assumed in the item. No new pushout construction or arbitrary-base-change preservation of scheme pushouts is asserted. In fact the supplied finite surjections and cartesian square suffice for the fibre argument. The additional nodality, flatness, trait, smooth-branch and geometric-fibre-pushout hypotheses cause no problem and have not been removed.

I read the current chapter and the recorded unit, the current main-20261015 direct-image proof (3), and the parent common-nodal-model proof step 6. This item is the connectedness subargument on that route. The blueprint ancestor tool returns None, as recorded in the live item's inherited from.node; I preserved it and its via list. Whole-DAG searches and blueprint_refs searches for pinching, connected fibres and connectedness found no existing node stating this theorem. There are no new ids requiring a same-tag duplicate comparison.

## Mathlib searches

Read all five actual Q133 search results in searches.jsonl: two semantic phrasings in LeanFinder, one LeanSearch query, Loogle with GeometricallyConnected and IsProper, and the recorded grep in AlgebraicGeometry. The hits concern properness, general base-change maps, covering spaces, profinite sets and Galois categories. I read the Mathlib geometrically-connected source: it defines/testing geometric connectedness and gives open-map results, but does not prove the pinching assertion. These searches supplement, and do not replace, the item's inherited Q02 searches. No search was invented and no failed service was called a negative result.

## Review by Q133

I checked delivery-errors B--E against the actual node statements and the sources. No new node restates a clause of the item: every fibre calculation is written in the item's own proof. The only elementary-marked step is the two-image separation argument, with the fibre-product universal property cited. All six steps are under 800 characters; none conceals a long unextracted comparison.

For step 1 I read morphisms.tex labels lemma-composition-proper (01W3), lemma-locally-projective-proper (01WC) and lemma-image-proper-scheme-closed (01W6). The proper-permanence node explicitly gives composition; the projective-implies-proper node gives properness of the two structure maps; the proper definition includes separatedness; and proper-over-separated explicitly applies to an S-map from a proper S-scheme to a separated S-scheme. Thus p is proper without needing h's properness to descend through the pinching square. The length-zero h is the identity, whose properness follows directly from the proper definition.

For step 2 I read topology.tex lemma-connected-fibres-quotient-topology-connected-components (0377) and morphisms.tex lemma-base-change-proper (01W4). The connected-preimage node explicitly includes connectedness of the source when its quotient target is connected; I use exactly that clause. The base-changed link has all point fibres nonempty connected because they are field extensions of the original link fibres. Surjectivity follows point by point, closedness is in the proper definition, and the quotient condition is written out. This proves the induction for arbitrary field-valued c, including nonclosed c, so disconnected C or intermediate V_j are never assumed connected.

For step 3 I read the statements of finite-morphism-permanence and surjective-base-change and their source assertions 01WL and 01S1. They give exactly the finite surjective E -> Z after arbitrary base change; no scheme pushout needs to commute with this base change. The assumed complement isomorphism gives the unique C-point over an off-conductor x. Fibre-product universality identifies E with the h-fibre, so the continuous-image connectedness argument is a two-line separation argument, written in the step.

For step 4 I opened the full etale-geometric-fibre-compact-sections statement: its FIRST clause gives the canonical finite coproduct of Spec Omega for a separated quasi-compact etale map. I read its source assertion 09Z9(1) and algebra.tex lemma-etale-over-field (00U3), which explains the finite separable field factors. Its sheaf assertions are unused. B -> N is finite, so finite-proper and the proper/finite-type definitions give separatedness and quasi-compactness. Constant degree two makes the number of geometric sheets two. The closed-immersion ideal vanishes at x, so x really factors through N as a scheme point, not merely as a topological assertion. The assumed cartesian square gives C_x=B_n; I then use the finite-coproduct base-change node, whose statement explicitly gives the canonical isomorphism and summand projections. Thus E is the disjoint union of the TWO h-fibres. This is not a claim that h^{-1}(B)=B: h may contract extra components to marked points.

For step 5 I read more-morphisms.tex proposition-pushout-along-closed-immersion-and-integral (0E25), including its set-quotient construction. Here only the defining relation ai=bj, already supplied by the pushout hypotheses, is needed. Branch compatibility h i_W=i_C ensures that the specified marked points belong to the corresponding F_i. Their Y-images equal the same N-point and their Omega-projections are the identity, so they give the SAME Z-point by fibre-product universality. Connected images meeting at that point cannot occupy different sides of a clopen separation. Their union covers Z by step 3, so the separation is trivial. This proof works if the two branch fibres originally lie on different components of W.

For step 6 I read the algebraic-closure criterion node and its cited varieties.tex labels lemma-characterize-geometrically-connected (0387) and lemma-geometrically-connected-check-after-extension (054N). Its statement permits any scheme over the residue field and explicitly gives connectedness after all field extensions from connectedness over the algebraic closure. Thus it applies to each p-fibre. Proper-permanence then gives p_s proper, whose fibres are such field extensions by fibre-product universality. The same quotient-connectedness node applies to the whole nonempty connected X_s and gives Y_s nonempty connected. Neither connectedness of C_s nor of W_s is used.

Edge cases checked explicitly: m=0 reduces the induction to Spec L and the pushout map to the identity; empty B,N removes the node case; two disjoint projective lines pinched at one point give a connected pushout with disconnected normalization and satisfy the same two-image argument; contracting a connected exceptional tree through a branch still gives meeting connected images, and the proof never incorrectly identifies that entire h-fibre with the marked point. Nonclosed x lies off the finite etale conductor on its geometric base and is handled by the complement case. A characteristic-two degree-two etale cover splits over an algebraically closed point just as in any characteristic; no order-two group averaging or inseparable quadratic field argument is used.

Generic tool uses declared in split_report: projective-implies-proper, the first clause of etale-geometric-fibre-compact-sections, and the algebraic-closure test. Other cited statement nodes are existing Mathlib leaves. I checked all their statements directly, copied complete verbatim statements into citations.json, retained all imported metadata, and wrote no Lean or repository file.

## Not duplicates

No new nodes.

## Unfinished work

None in the natural-language split. Server review_split passed, and deliver.py --no-push exited successfully with OK at 6f0a51dccff. The required preflight, including the DAG and split checks, passed. This direct-delivery brief authorizes the push following that completed dry run.
