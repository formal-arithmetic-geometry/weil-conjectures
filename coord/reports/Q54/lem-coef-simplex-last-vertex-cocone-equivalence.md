# Q54 stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-simplex-last-vertex-cocone-equivalence.json`: statement; split into nine proof steps. The statement and its sole statement dependency are unchanged. No matching Mathlib theorem was found.
- `dag/nodes/sec-six-functors/lem-coef-decomposition-simplex-lift-right-anodyne.json`: new statement-only node, unsplit; the general criterion of HTT Proposition 4.2.3.8. No Mathlib match.
- `citations.json`: thirteen verbatim statement excerpts, one for each proof-step citation.
- `searches.jsonl`: actual search-command records, retained as produced. `write_split.py` is a sandbox-only preparation script, not a delivery file.

## Attachments

None. I searched the project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact item tag, last-vertex spellings, simplex-category and decomposition terminology. No project declaration states the item or the new criterion. The item has no recorded upstream declaration. Master source is not treated as evidence of a finished proof.

## Wanted literature

WANTED: Jacob Lurie, *Higher Topos Theory*, Notation 4.2.3.1 (pp. 248-249), Proposition 4.2.3.4 (pp. 249-251), Notation 4.2.3.7 and Proposition 4.2.3.8 (p. 252), Lemma 4.2.3.13 and Proposition 4.2.3.14 (pp. 254-255), and Proposition 4.1.1.7 (p. 226), for the item and the new simplex-lift criterion. The online Harvard PDF was read directly; there is no archived HTT PDF in the named literature tree. Its physical PDF page numbers are 17 greater than the printed page numbers. The item's proof is therefore marked `proof_origin.by = agent`. These are simplicial homotopy and infinity-category results with no asserted Stacks-tag analogue. No SGA source is used.

## Corrections and interpretation

No statement dispute was found. The imported node was statement-only. Its historical search entries and blueprint ancestry were retained, and this worker's executed searches were appended. The shared repository initially lacked this recently created node; it appeared in the automatic refresh before any copy or edit was made.

The existing `lem-coef-simplex-category-last-vertex` proves only a weak homotopy equivalence of underlying simplicial sets. That is insufficient to obtain restriction equivalences for cocones into arbitrary quasicategories. I did not use that false inference. The proof instead follows exactly the decomposition-space argument of HTT 4.2.3.14. It uses the already stated decomposition construction and the already stated fixed-apex local-colimit theorem; it does not extract undocumented constructions from a cited proof.

The existing directed-cover criterion cannot be applied: the simplex category is not a directed poset, and the maps of its standard simplices into X need not be injective. The new node keeps the arbitrary-category and degenerate-lift hypotheses of 4.2.3.8. The worker's steps supply the nontrivial verification of those hypotheses rather than moving last-vertex cofinality into another node.

The chapter and unit records were read. This is not their key node, so neither record was changed. I read the current main-20261015 statement and proof of `prop-coef-integral-exceptional-adjoint`, including its paragraph-2 derived-Hom calculation, and retained the inherited ancestry through the filtered-poset replacement chain. All cited proof statements are in the same unit, except the already-Mathlib nondegenerate-decomposition leaf; there is no new off-route tool use.

## Unfinished work

No part of the item's argument is postponed except the explicitly cited general statement-only criterion, which joins the queue according to the one-level split rule. That criterion has no proof sketch hidden in its statement. It can be split later by the face-stable filtration in HTT 4.2.3.8, using the existing contractible-join and join-pushout right-anodyne results. This describes the intended downstream work, not a claimed proof of that new node.

## Not duplicates

lem-coef-decomposition-simplex-lift-right-anodyne vs lem-coef-directed-decomposition-right-anodyne: the existing result assumes a nonempty directed poset and an increasing cover by simplicial subsets. The new criterion permits arbitrary ordinary categories and noninjective maps, with separate hypotheses on categories of lifts and degenerate lifts; the simplex-category diagram here does not satisfy the existing result's assumptions.

lem-coef-decomposition-simplex-lift-right-anodyne vs lem-coef-decomposition-local-colimit-cocones: the existing result constructs the decomposition simplicial set and gives restriction along its base when the extension has local colimit cones. The new result concerns the other inclusion, from the indexing nerve, and gives right anodyneness from simplex-lift conditions, with no quasicategory or local-colimit input.

lem-coef-decomposition-simplex-lift-right-anodyne vs lem-coef-simplex-category-last-vertex: the existing result gives a weak homotopy equivalence for one specific last-vertex map; the new result is a right-anodyne inclusion criterion for an arbitrary decomposition diagram and has no last-vertex-map conclusion.

lem-coef-decomposition-simplex-lift-right-anodyne vs lem-coef-infinity-anodyne-cocones: the existing result takes right anodyneness as a hypothesis and concludes cocone restriction equivalences. The new criterion proves right anodyneness for a decomposition inclusion from lift-category hypotheses.

I searched the whole DAG for the source proposition and for simplex-lift, cofinal and decomposition terminology, and ran whole-blueprint searches for simplex, decomposition and right anodyne. No existing node or blueprint statement supplies the new general criterion. The matches for Proposition 4.2.3.8 are its directed-cover specialization or applications. No common Stacks tag is claimed.

## Mathlib search reading

For the item and the new node I used the required msearch command with LeanFinder, Loogle, LeanSearch and grep. I tried a second semantic phrasing for each, and a second relevant Mathlib directory for the criterion. All services answered successfully. Exact query text and returned record digests are copied from searches.jsonl into the corresponding mathlib_searches entries; existing imported searches were retained, not falsely attributed to this worker.

I read Mathlib/AlgebraicTopology/SimplicialSet/Nerve.lean:34-72 and Simplices.lean:13-21,42-45,118: the hits define ordinary nerves and distinguish the simplex preorder from the full category of simplices. They do not prove the item's cofinality assertion. For the criterion I read AnodyneExtensions/Basic.lean:16-45,64-83: its anodyne extensions use all horns and do not state the right-anodyne decomposition criterion. Other hits concern ordinary nerves, horn colimits, coskeleta or unique nondegenerate decompositions. None is an exact match or one-line specialization of either requested statement.

## Review by Q54

I read delivery-errors B through E in full and checked the files against their mathematical failure cases. For the item I read HTT 4.2.3.13-14 and its invocations of 4.2.3.4 and 4.2.3.8 directly in the online PDF. For the new node I read the definitions in 4.2.3.1 and 4.2.3.7 and the exact two hypotheses and right-anodyne conclusion of 4.2.3.8, together with its face-stable filtration proof. This is a genuine general intermediate lemma, not a renamed clause of the item, and it is longer than a two-line consequence of the cited local-colimit theorem.

Step 1 uses the statement of `lem-coef-decomposition-local-colimit-cocones` for the full definition of H and its specified local cone maps. I verified that it allows arbitrary small ordinary I and arbitrary maps over X. The finite-ordinal arrow equation makes F a functor; smallness is checked by counting its simplex and finite-map sets.

Step 2 uses the simplicial conventions of `def-cbc-enhanced-diagrams-cones` and gives the construction itself. I checked monotonicity across the cut and every operator: if the final object disappears the tail map c satisfies cv'=v theta, and the structural simplex changes by that same c. If one block disappears the pure-simplex rule is explicitly checked. The restriction to each local cone repeats the last vertex; the restriction to the pure indexing nerve is the exact map in the statement, not just a homotopic replacement. No theorem about all weak homotopy equivalences is used.

Step 3 cites the actual repeat-last-vertex clause in `lem-coef-infinity-final-index-colimit`, which states this specified cocone is colimiting, and then the exact fixed-apex equivalence in `lem-coef-decomposition-local-colimit-cocones`. Every one of its local colimits is provided, the extension is the actual q=pr, and the base is the actual X. No arbitrary colimit in E has been assumed. Step 4 is the explicit retraction calculation on the functor and right-pinched mapping-space definitions; bijectivity on components and based homotopy groups proves the inverse map is an equivalence, including empty spaces.

Step 5 reads the definition of I_z in the new criterion and identifies its actual objects and arrows with simplex factorizations. Its initial object really has a unique map s to each factorization. `lem-coef-nerve-natural-homotopy-equivalence` explicitly allows noninvertible natural transformations and supplies contractibility of this nerve. I read its full statement before citing it.

Step 6 checks the degenerate lifts in a standard simplex: they are the noninjective ordinal maps, not the degenerate structural simplices tau in X. The image-factorization functor is written out on objects and arrows. Its natural transformation has direction JR to the identity, and RJ is the identity, so the nerve-homotopy node applies exactly. In particular no unjustified adjunction or deformation-retraction result is quoted.

Step 7 cites the full uniqueness statement in `lem-weil-pbc-simplicial-set-nondegenerate-decomposition` to find the terminal object of the surjective-factorization category. The unique arrow u satisfies us=t by that uniqueness and is itself unique because s is surjective. Since z is degenerate, t is a proper surjection, so this terminal object belongs to B_z. I checked the natural transformation to its terminal constant functor against the nerve-homotopy node. Both nerves D_z and I_z are contractible, which proves their actual inclusion is a weak homotopy equivalence.

Step 8 applies exactly the two verified hypotheses of the new criterion, and then the cocone-restriction clause of `lem-coef-infinity-anodyne-cocones`. That node does not assume either indexing simplicial set is a quasicategory. Step 9 is strict composition of precomposition maps, hence proves the actual restriction along ell_X. Its empty case is handled directly. I checked every citation against the cited statement, not its proof, and supplied thirteen verbatim excerpts in citations.json.

Small cases checked: X empty gives empty simplex category and identity restriction; X a point includes every degenerate simplex and yields the expected contraction; X=Delta^1 recovers the standard last-vertex direction; noninjective simplex maps require the image retraction in step 6 rather than a poset argument. For the new criterion, I empty and K empty gives an identity; I empty and K nonempty fails the contractible-lift hypothesis as it should; I terminal with K_a=K gives K_F=K join point, with identical degenerate-lift categories. The distinction between degenerate z and degenerate lift w was retained. There are no new hypotheses on the item, no coefficient-category identifications, no target edits and no source-route change.

The new record has empty proof and proof_deps, complete source and ancestry, all required searched notions and no unsupported Mathlib leaf claim. All new statements are standalone, with their objects introduced and hypotheses explicit. The report and files are left for the independent second reader; no delivery push is authorized for this worker.

## Second reading by Q54

- Item statement: checked against HTT Proposition 4.2.3.14, Lemma 4.2.3.13, and Proposition 4.1.1.7; every hypothesis and the empty-simplicial-set case agree.
- New node `lem-coef-decomposition-simplex-lift-right-anodyne`: checked against HTT Notation 4.2.3.1, Notation 4.2.3.7, and Proposition 4.2.3.8; the arbitrary category, noninjective maps, lift categories, degenerate subcategories, and right-anodyne conclusion are all present.
- Step 1: checked the explicit decomposition data and local-colimit construction against `lem-coef-decomposition-local-colimit-cocones`; the functor and smallness checks are supplied.
- Step 2: checked the retraction formula and all simplicial-operator cases against HTT Lemma 4.2.3.13; the terminal tail, disappearing blocks, and degeneracies are explicit.
- Step 3: checked the repeat-last-vertex cocone against `lem-coef-infinity-final-index-colimit` and the exact local-colimit hypotheses against `lem-coef-decomposition-local-colimit-cocones`; verdict correct.
- Step 4: checked the fixed-apex mapping-space retraction against `def-cbc-enhanced-diagrams-cones`; the strict identity and empty-space case justify equivalence.
- Step 5: checked the factorization category, initial object, and nerve contraction against HTT proof p. 254 and `lem-coef-nerve-natural-homotopy-equivalence`; verdict correct.
- Step 6: checked the noninjective/surjective factorization, image functor, induced arrows, and natural transformation against HTT p. 255; the arrow directions and degeneracy distinction are correct.
- Step 7: checked the unique nondegenerate decomposition and terminal surjective factorization against `lem-weil-pbc-simplicial-set-nondegenerate-decomposition` and HTT p. 255; verdict correct.
- Step 8: checked both hypotheses and the right-anodyne-to-cocone restriction application against the new criterion and `lem-coef-infinity-anodyne-cocones`; verdict correct.
- Step 9: checked strict composition `ra = ell_X` and the empty case against `def-cbc-enhanced-diagrams-cones`; verdict correct.
- New-node form: statement-only, self-contained, TeX escaped once, source and blueprint ancestry recorded, no proof or proof dependencies, and searches recorded; no Mathlib leaf is claimed.
- Existing-node audit: searched the shared DAG for simplex-category, decomposition, cofinal, and right-anodyne results; the new criterion is not duplicated, while all cited existing nodes are the statements actually used.
- Small cases: checked empty $X$, point $X$, $\Delta^1$, noninjective simplex maps, and empty/terminal indexing categories; no edge-case change was needed.
- Changes made: none to statements, proof steps, citations, or node metadata; appended this independent audit and ran additional required Mathlib searches, which were logged in `searches.jsonl`.
