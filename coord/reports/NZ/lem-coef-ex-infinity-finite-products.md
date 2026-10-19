# Stage-1 worker report: lem-coef-ex-infinity-finite-products

## Files written

- `dag/nodes/sec-six-functors/lem-coef-ex-infinity-finite-products.json`: statement, split into nine steps; mathematical statement unchanged. Added statement dependencies for ordinary nerves and the sequential-colimit convention.
- `dag/nodes/sec-six-functors/lem-coef-subdivision-face-poset-calculus.json`: statement-only, unsplit. Subdivision adjunction and the nerve-of-faces description with its image-of-faces action. No full Mathlib match; the single adjunction is present, but the face comparison is explicitly a TODO in the pinned subdivision file.
- `dag/nodes/sec-six-functors/lem-coef-ex-comparison-weak-equivalence.json`: statement-only, unsplit. The one-step comparison is a realization weak equivalence. No Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-filtered-colimit-weak-equivalences.json`: statement-only, unsplit. Stability of realization weak equivalences under arbitrary small filtered colimits of simplicial arrows. No Mathlib match.
- `citations.json`: one verbatim statement quotation for every citation of every proof step.
- `report.md`: this report. Search outputs and the exact msearch log are retained beside it.

Three new nodes; zero Mathlib leaves. No unit record is changed: this item is an auxiliary descendant, not the key statement of its unit.

## Attachments

None. Searches for the exact blueprint tag, ExInfinity/exInfinity/ex_infinity/Ex-infinity, subdivision, last-vertex, and Kan replacement in the project sources found no declaration stating this item, nor the new inputs. No compiler, Lake command, Lean file, or git command was run by this worker. The upstream master was used only as a read-only reference, not as evidence that a sorry declaration is proved.

## Wanted literature

WANTED: an archived Kerodon, Section 3.3.6 (00ZA), especially Propositions 3.3.6.2, 3.3.6.4, 3.3.6.7 and 3.3.6.9 (00ZK), for lem-coef-ex-infinity-finite-products.

WANTED: an archived Kerodon, Proposition 3.3.3.17 (00YL), Corollary 3.3.3.4 and Construction 3.3.4.3 (00YU), for lem-coef-subdivision-face-poset-calculus.

WANTED: an archived Kerodon, Theorem 3.3.5.1 (00Z2), for lem-coef-ex-comparison-weak-equivalence.

WANTED: an archived Kerodon, Proposition 3.2.8.3 (00XE), for lem-coef-filtered-colimit-weak-equivalences.

All these online originals were opened and read. No corresponding archive was found among the repository's literature files; nothing was downloaded into the read-only literature directory. The item's proof_origin is therefore agent, with the online source and the absence of the archive made explicit. These are Kerodon tags, not Stacks tags. The finite-limit interchange is genuinely Stacks 002W, categories.tex, lemma-directed-commutes, whose text I read locally. No SGA source is used.

## What was wrong or missing

The item had no proof. Its statement is mathematically correct, including preservation of finite limits and the terminal comparison, so there is no STATEMENT-DISPUTED and no weakening. Its ancestry records the enhanced coefficient-adjunction foundation; I checked the current main-20261015 proof of prop-coef-integral-exceptional-adjoint, paragraph 2, against the older ancestor text. The displayed derived-adjunction calculation and the following unit/counit compatibility are unchanged for this purpose. The new work supplies the assigned technical input beneath that route, without changing the chapter or unit.

I did not replace the item by a generic fibrant replacement, which need not preserve finite limits, or by the ordinary homotopy-category functor found in searches. Nor is a one-step Ex asserted to be Kan. The finite horn is instead filled one stage later, with the construction written in the item's steps.

The initial Loogle patterns `SSet.ex, WeakEquivalence` and `SSet, IsStableUnderFilteredColimits` returned unknown identifiers. They are recorded as invalid patterns, not as evidence of absence. I reran valid searches for `SSet.ex` and `CategoryTheory.MorphismProperty.IsStableUnderFilteredColimits`. Every recorded search is an actual msearch invocation; output text is copied unchanged. The semantic services were available in this run. UTC dates on the search log can be 2026-10-16 while the local work date is 2026-10-17.

## Not duplicates

lem-coef-subdivision-face-poset-calculus vs lem-weil-pbc-presheaf-pullback-left-exact: the common four-character string 00YU denotes different tags in different projects. The existing node is the Stacks theorem on a presheaf Kan extension and left exactness under a finite-limit-preserving site functor. The new node uses Kerodon's last-vertex construction and subdivision of finite ordered simplicial complexes. The existing statement neither constructs this subdivision nor identifies its face poset.

The whole-DAG statement search found no existing subdivision/last-vertex lemma or filtered-colimit closure theorem for simplicial weak homotopy equivalences. The whole-blueprint searches for subdivision, last vertex, face poset, filtered colimits, and weak homotopy equivalence found no node stating any new input. In particular, the existing filtered-colimit/finite-limit theorem is reused directly for the interchange; no new finite-products lemma is created. The realization finite-support theorem is about compact topological maps, not filtered colimits of arbitrary simplicial arrows. The one-step Ex theorem concerns a single transition and supplies neither the Kan condition nor the finite-limit conclusion of this item. The face-calculus node contains no horn-extension assertion: the actual finite-poset extension is proved in steps 2–4 of the item. Thus none of the new nodes is a clause of the item merely relabelled as an input.

## Review by NZ

I read coord/brief-stage1.md, the stage-1 contract, the three blueprint levels in SETUP.md, delivery-errors B–E in full, coord/dag-sync.md, GOAL.md, the worker role, the chapter and unit records, and the ancestor proof in both relevant blueprint snapshots. I checked the imported statement against the online Ex definition (00XN), the last-vertex construction (00YU), and the Ex-infinity section (00ZA). Its transition really is j at each successive object, rather than an unidentified map involving Ex(j). The geometric-realization notion of weak equivalence agrees with the existing Kan–Quillen node and with the online sources.

For the three new nodes I read respectively Kerodon 00YL and the subdivision adjunction/last-vertex constructions, 00Z2 with its comparison-map proof, and 00XE with its arrow-category filtered-colimit statement. Their statements introduce their objects explicitly. In particular the face-calculus node specifies arrows in the category of simplices, the colimit construction of Sd, the finite poset, the downward-closed family of nonempty chains, and the monotone-map hypothesis needed by its image-of-faces rule. The filtered-colimit input assumes a small filtered index category, not an arbitrary large category. None of these new nodes carries a proof or a proof sketch in its statement.

For step 1 I checked the cited simplicial-set definition and wrote the actual section of each standard-simplex last-vertex map. This proves monicity without assuming it from a replacement theorem. It also makes passage to a common stage in step 5 legitimate. In step 2 I checked every clause of the new face-calculus statement: the horn is the complex with face poset Q; N(Q) and N(P) are finite ordered complexes; applying its subdivision formula again gives precisely Ch(Q) and Ch(P). I added the explicit check that the image-of-maxima face is in Q, which is a hypothesis of the cited image-of-faces rule.

For step 3 I verified that the modified maximum formula lands in Q even on chains meeting one or both removed faces. The largest allowed member omits a vertex other than i, and adjoining i does not supply that missing vertex; with no allowed member the output is the singleton {i}. Images of subchains are subsets, so the map is monotone even though the modified vertex function is not monotone. I enumerated every strict nonempty chain in the subset posets for dimensions 1–4 (5, 25, 149, and 1081 chains per horn respectively), checking the output belongs to Q and the restriction on Ch(Q) agrees with the unmodified maxima formula. This is an additional finite sanity check, not a substitute for the written general proof.

For step 4 the face-calculus node states both the natural adjunction and that j transposes to lambda. I checked the two transposes separately: the horn restriction is f lambda_A on the first transpose, hence bar(f) Sd(lambda_A) on the second. It is not lambda_(Sd A), which would be the wrong map. This check is written explicitly rather than hidden under a claim of compatibility. The cited face statement therefore supplies exactly the structural data used in steps 2–4, and those steps themselves construct the extension.

For step 5 I read the Kan–Quillen node's horn and fibrant-object clauses. It really permits n=1 and both outer horns and does not impose a dimension-zero nonemptiness condition. The horn is generated by finitely many codimension-one faces, so choosing representatives and checking overlaps is a finite operation. Injectivity from step 1 checks these overlaps at the common stage. Raising the stage to m>=1 makes X_m=Ex(X_(m-1)), exactly as required by step 4. Empty K is harmless because no nonempty horn maps into it. I did not use the proof of the Kan–Quillen node as an extra black box.

For step 6 I checked that the one-step comparison node gives a weak equivalence for every simplicial set, including the non-Kan intermediate stages. Composition is part of the cited model structure. The filtered-colimit node is applied to a natural transformation of two diagrams over the small directed category N, and gives exactly the degreewise colimit map. I wrote why the constant diagram's colimit is K and why the induced map is the chosen stage-zero unit.

For step 7 I used only the cited definition of simplicial sets: maps into the degreewise set of compatible tuples are compatible families of maps. This supplies the inverse of the Hom/limit comparison and checks its operators, including the empty diagram. In step 8 I opened and read the existing filtered-colimits/finite-limits node, and the local Stacks 002W source. The node states the canonical bijection for a small filtered category and a category with finitely many objects and arrows; our indices are N and the given finite J. Its canonical-map clause is what makes the interchange commute with simplex operators. It is already a Mathlib leaf, so this off-unit generic set-theoretic input requires no unit-route replacement. In step 9 I wrote the projection equations and the equality for the unit component by component; the empty-product assertion follows from uniqueness of a map to the terminal object.

I checked the quotations in citations.json against the actual statement strings, including hypotheses and the part used in each step. I also checked that proof_deps is the union of the step uses, and that stmt_deps includes the colimit convention and ordinary nerve notion in addition to the original simplicial-set and Kan–Quillen dependencies. New nodes inherit the item's chapter and unit, carry the exact ancestor/via chain, have searched same_as lists, and have no maintainer-owned review metadata. No target statement or definition was changed.

## What remains

No part of this item's one-level split is intentionally left unfinished. The three statement-only nodes are the next stage-1 items, as required; they are not claimed proved here. The second reader must review this sandbox and perform the real delivery. This worker performs only --no-push.

## Second reading by NZ

- Item statement: checked every clause against Kerodon 00XN, 00YU, and 00ZA (Construction 3.3.6.1 and Propositions 3.3.6.4, 3.3.6.7, 3.3.6.9); correct and unchanged, including the specified transitions, finite limits, terminal object, and unit compatibility.
- Step 1: checked the cited simplicial-set definition and Kerodon's section-of-last-vertex argument; correct for degree zero too. Added the stagewise construction of the induced colimit functor and natural unit.
- Step 2: checked the actual face-calculus statement against the horn face sets; its image-of-faces clause applies because maxima stay in the largest allowed face. Correct.
- Step 3: checked the actual face-calculus statement and the modified-maxima construction; the omitted vertex differs from i, so adjoining i is harmless. Correct.
- Step 4: checked the adjunction and last-vertex clauses actually stated by the face-calculus node; the two transposes give Sd(lambda_A), with all domains correct. Correct.
- Step 5: checked the horn and fibrant-object clauses of lem-coef-kan-quillen-right-proper; finite face representatives glue using injectivity. Correct for both one-dimensional horns and the empty simplicial set.
- Step 6: opened both new weak-equivalence inputs and the Kan–Quillen node; their statements provide precisely the one-step equivalences, composition, and filtered arrow colimit used here. Correct, with N small, filtered and nonempty.
- Step 7: checked the cited simplicial-set definition; compatible tuples give both directions of the Hom/limit bijection. Correct for the empty diagram as well.
- Step 8: opened the filtered-colimit/finite-limit node and Stacks categories.tex, Tag 002W, label lemma-directed-commutes (line 2182). Both index hypotheses and the canonical map agree; simplex operators act on the same representatives. Correct.
- Step 9: checked the projection equations against steps 1 and 8; uniqueness of tuple maps proves the unit equation. Correct, including the empty product.
- New node lem-coef-subdivision-face-poset-calculus: checked Kerodon 00YL, 00Y9, 00YJ, 00YM, 00YN and 00YU. Its finite ordered subcomplexes have the required nondegenerate-face property; image-of-faces also covers maps collapsing vertices. Repaired unintroduced P', F', A' and made Ex's operators explicit; otherwise correct. Empty complexes, a singleton poset, a single edge and its constant vertex map pass. B1–B7 checked: statement only, explicit objects, actual definition dependencies, single TeX escaping, precise source tags, no unsupported Mathlib leaf or tag-dependent meaning.
- New node lem-coef-ex-comparison-weak-equivalence: checked the statement and comparison formula against Kerodon 00Z2 and 00YU; no Kan hypothesis is needed. Correct for the empty and one-point simplicial sets. B1–B7 checked; no proof is hidden in the statement and both required definition nodes actually define the notions used.
- New node lem-coef-filtered-colimit-weak-equivalences: checked Kerodon 00XE's arrow-category formulation; arbitrary small filtered diagrams are allowed, without monic transitions. Correct for a singleton index category and constant empty/point diagrams; filteredness excludes the empty index category. B1–B7 checked, including the actual colimit/filteredness and realization definitions.

Independent duplicate and leaf checks: searched the whole shared DAG by the Kerodon tags and by subdivision, barycentric, last vertex, face poset, and filtered weak-equivalence phrases; searched both complete blueprint snapshots, all chapters. No existing node states a new input. Stacks 00YL concerns conservative points, and Stacks 00YU concerns presheaf pullback, so those tag collisions are not duplicates. Neither the model-localization statements nor the realization/CW statement gives filtered closure of simplicial weak equivalences. Read the pinned Mathlib Subdivision.lean (all 81 lines), NerveNondegenerate.lean and Monomorphisms.lean: the adjunction exists, the general face comparison remains TODO, and the colimit instance concerns monomorphisms. The new nodes are substantive smaller inputs, not clauses of the item restated.

Ran my own msearch queries with different phrasing: “Barycentric subdivision carries a finite simplicial subcomplex of a poset nerve to the nerve of its nondegenerate simplex category”; “Weak homotopy equivalences in SSet are closed under filtered colimits of morphisms”; “The natural transformation from the identity simplicial set functor to its extension functor Ex is a weak equivalence”; and two independent whole-Mathlib grep patterns for weak equivalences/colimits/Ex and nerve/nondegenerate/subdivision/lastVertex. Actual results and digests are in searches.jsonl and copied into the relevant node records. All services succeeded. The first semantic query returned nondegenerate-nerve descriptions, the second monomorphism stability and generic coproduct results, and the third generic adjunction/realization facts: none states the input. Read-only searches of both project source checkouts by ids and terminology found no attachment.

Also independently enumerated all strict nonempty subset chains for n=1,2,3,4 (5,25,149,1081 respectively), for every horn index: the modified-maxima set always lands in Q, restricts to the required maxima set, and respects subchain inclusion. This checks small cases alongside the general written argument. Read the current main-20261015 ancestor's adjunction proof; the technical input serves its displayed derived-adjunction calculation and units/counits, without changing that route. No SGA source is used.

Changes: introduced the second finite-poset/complex data before use (B2); specified Ex's simplex operators (B2); added the exact source tags for the adjunction, nerve example and functoriality (B5); wrote the induced Ex-infinity functor and unit explicitly; added actual independent search metadata; replaced partial quotations with full verbatim statements for all ten citations. All nine original proof steps and all three necessary new nodes remain. The first worker's review is retained. No statement dispute, target change, compiler, Lean edit, live-project write, or direct git command was needed.

WANTED additionally: archived Kerodon Corollary 3.3.3.4 (00Y9), Examples 3.3.3.14 (00YJ) and 3.3.3.18 (00YM), and Remark 3.3.3.21 (00YN), for the face-calculus node. Read online in the Subsection 3.3.3 source; this supplements the worker's existing wanted list.
