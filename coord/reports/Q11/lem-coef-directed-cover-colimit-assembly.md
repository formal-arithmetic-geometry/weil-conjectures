# Stage-1 worker report: lem-coef-directed-cover-colimit-assembly

## Files and result

The item is split into six proof steps. There are two new, statement-only, unsplit nodes and zero Mathlib leaves:

- `dag/nodes/sec-six-functors/lem-coef-directed-cover-colimit-assembly.json`;
- `dag/nodes/sec-six-functors/lem-coef-contractible-join-right-anodyne.json`;
- `dag/nodes/sec-six-functors/lem-coef-join-slice-cocone-comparison.json`.

`citations.json` contains all 17 step/node pairs with verbatim quotations from the actual cited statements. `searches.jsonl` contains the wrapper's search evidence. Only this sandbox was edited. No Lean was written, no compiler/Lake/build was run, no worker git command was run, and no delivery was pushed. The required delivery dry run uses its own temporary worktree.

The imported statement is mathematically unchanged, including its empty-shape clause. Its doubled TeX command backslashes were normalized by the earlier attempt. No statement dispute is necessary.

## Attachments and searches

There is no attachment. I searched the read-only slopmaster2 `WeilConjectures/` tree for the item id/docstring tag, directed-cover and coherent-colimit terminology, contractible joins, fat/join slices, `hocolim`, `homotopyColimit`, `rightAnodyne`, `RightAnodyne`, `fatJoin`, and `joinSlice`. The few directed-cover hits concern scheme gluing or compactness. None states this item or either auxiliary lemma. The master checkout was used only as reference material, never as evidence that a sorry declaration is proved.

I read the existing sandbox search log, then renewed each new node's LeanFinder, valid Loogle, wrapper grep and LeanSearch searches, including a second semantic phrasing. I also renewed the item's searches. The exact queries and wrapper results are recorded in each node; no query was invented. All renewed services answered successfully. Earlier unknown-identifier Loogle results remain recorded as such.

The right-anodyne queries return the all-horn Quillen class `SSet.modelCategoryQuillen.J`, cofibration/monomorphism results, ordinary categorical joins, and unrelated jointly-surjective cell maps. These signatures do not assert the one-sided-anodyne join theorem. The broader AlgebraicTopology grep found no right-anodyne/contractible-join declaration. The slice queries return ordinary `CategoryTheory.Join`, `StructuredArrow`, `Under`, and cocone equivalences, or ordinary homotopy-category results. Loogle's SSet cocones are colimit cocones in the ambient category of simplicial sets. The scoped Quasicategory grep returns license/underlying-category text. The assembly queries likewise return ambient SSet or ordinary scheme/poset colimits. None specializes in one line to a theorem about arbitrary coherent simplicial diagrams in quasicategories.

## Sources and blueprint

I read the chapter record `sec-six-functors`, unit record `sk-prop-sf-biduality-general`, the three-level rules in SETUP, GOAL, dag-sync, and the current `main-20261015` proof of `prop-coef-integral-exceptional-adjoint`. Its mapping-complex adjunction paragraph is the inherited blueprint ancestor; this generic filtered-subdiagram tool remains below that paragraph through the recorded ancestry. I did not change chapter or unit metadata or the coefficient-duality route.

For the item I read [HTT](https://people.math.harvard.edu/~lurie/papers/HTT.pdf), Notation 4.2.3.1, Lemma 4.2.3.3, the full proof of Proposition 4.2.3.4, Lemmas 4.2.3.5–4.2.3.6, Proposition 4.2.3.8, Remark 4.2.3.9 and Corollary 4.2.3.10, printed pp. 248–253. For the slice comparison I read the fat-join adjunction and Proposition 4.2.1.5, Proposition 4.2.1.6 and Corollaries 4.2.1.7–4.2.1.8, pp. 241–242. The item and both new nodes identify these places explicitly. These infinity-categorical assertions have no corresponding Stacks tag. No SGA source is used.

WANTED: an archived copy of HTT, those places, for the item and its two new nodes. The PDF was read online, not downloaded into the read-only repository. Accordingly the item's proof_origin remains agent, as the standing brief requires for an unarchived source. The actual Stacks simplicial homotopy fact is cited through the existing node for Tag 08NS, label `lemma-trivial-kan-homotopy`; I also read that proof in `literature/stacks-project/simplicial.tex`.

Whole-DAG searches used source numbers and mathematical terms; blueprint searches used `blueprint_refs.py search` for sharp join, fat join, anodyne, cocone, and directed cover, and `ancestor` confirmed `prop-coef-integral-exceptional-adjoint`. No imported node states either new lemma. Numeric matches in unrelated tags were checked in their source fields. The item's `blueprint.from.place` and both new nodes' places are specific; `same_as` is empty.

## Not duplicates

lem-coef-contractible-join-right-anodyne vs lem-coef-infinity-cone-mono-right-anodyne: the existing statement only joins with a point; the new statement allows an arbitrary weakly contractible second factor, needed for support-poset nerves.

lem-coef-contractible-join-right-anodyne vs lem-coef-infinity-pushout-join-saturation: the existing statement concerns weak saturation for inner-anodyne pushout-joins, without the weakly contractible factor/right-anodyne conclusion.

lem-coef-join-slice-cocone-comparison vs lem-coef-infinity-join-cone-calculus: the existing statement compares product-parametrized functor categories of cones; the new statement compares the join-adjoint slice, whose n-simplices use L star Delta^n, with coherent cocones and fixed-apex Kan fibers.

lem-coef-join-slice-cocone-comparison vs lem-coef-infinity-slice-right-fibration: the existing statement supplies the sharp slice fibration and, for a vertex diagram only, identifies its mapping fiber; it does not compare general sharp slices with coherent cocones.

lem-coef-join-slice-cocone-comparison vs lem-coef-infinity-slice-arrow-equivalence: the existing comparison fixes a single vertex diagram; the new statement allows any simplicial indexing shape and includes the fixed-apex equivalence.

lem-coef-join-slice-cocone-comparison vs lem-coef-infinity-blunt-sharp-join-equivalence: the existing statement concerns functor categories on two fixed joins, not their join-adjoint slices or their fixed-apex fibers.

lem-coef-join-slice-cocone-comparison vs lem-coef-join-slice-diagram-isomorphisms: the existing statement compares equivalence edges of diagrams in a slice over one vertex with those of right cones; it is not a sharp/fat slice comparison for a general diagram.

The existing `lem-coef-colimit-subdiagram-approximation` is a special cover indexed by kappa-small subdiagrams; it cannot establish arbitrary directed-cover assembly and is not cited in reverse. Neither new node restates a clause of the item. Neither is elementary: the first is HTT's general right-anodyne join theorem, and the second identifies two different simplicial slice models, including their fibers. Their proofs and proof_deps are empty, as required for unsplit children.

## Review by Q11

I checked the existing attempt directly against delivery-errors B–E and the open source passages, rather than relying on its previous review text.

Step 1 uses the new join-slice comparison for quasicategory structure, initiality, fixed-apex equivalence and naturality. It uses `lem-cbc-enhanced-functor-cone-calculus` for the mapping-space criterion and invariance under equivalence. The statements actually give these assertions. A weak equivalence of the fixed-apex Kan spaces supplies a representative equivalent to each prescribed cocone with the SAME apex; equality of arbitrary sharp and fat representatives is not assumed. All indexing sets are small; the assumed small-colimit completeness supplies the global colimit.

Step 2 uses clause (4) of `lem-coef-infinity-relative-cone-equivalence`, which explicitly supplies opposites and reversed mapping-space equivalences; `lem-cbc-terminal-boundary-extension`, which supplies the terminal-last-vertex boundary criterion; and `def-weil-pbc-trivial-kan-fibration`, whose dimension-zero condition is surjectivity on vertices. The joined boundary is the boundary in dimension n+m+1, which is always positive. Passing to opposites makes its first initial vertex the last terminal vertex. This explicit boundary calculation is elementary from these cited statements; it proves every required lift, including n=m=0. It is not left as another child node.

Step 3 uses `lem-coef-infinity-monomorphism-boundary-cells` for a small relative skeletal filtration and the new slice comparison for the quasicategory in which the boundary is filled. I checked the attachment: a chain i_0<...<i_n uses K_i0, not K_in or an intersection. Deleting its first final-block vertex is allowed precisely by K_i0 subset K_i1. The boundary's first vertex is the chosen initial local colimit, so step 2 applies. Limit stages are literal unions of compatible maps. The actual edges and higher simplices of the resulting q give the coherent apex diagram. I expanded the earlier attempt's last word “transport”: compatibility paths are concatenated with the inverse fixed-apex comparison equivalence at the source and the restricted comparison equivalence at the target. Thus compatibility concerns the prescribed cocones, not unrelated representatives.

Step 4 uses the trivial-fibration definition, `lem-weil-pbc-trivial-kan-homotopy-equivalence` (its statement supplies a section and simplicial homotopy), the slice comparison including naturality/fibers, and the cone-calculus criterion. For each cell I checked the restriction square by the defining join-slice simplices: both extension problems concern K_i0 star (Delta^n star Delta^m) with the same prescribed boundary. The n=0 case handles vertex cells. Recursive lifting with union at limits proves the whole restriction map trivial; no claim that an arbitrary strict inverse limit computes a homotopy limit is used. Pulling back at a fixed apex preserves the same lifts. The resulting equivalence is induced by restriction of the actual lifted cocone, so the cited mapping-space criterion proves it colimiting.

Step 5 uses `lem-cbc-filtered-nerve-weak-contractibility` with all its hypotheses checked: coverage makes each support poset nonempty, monotonicity makes it upward closed, directedness supplies common successors, and uniqueness of poset arrows supplies the parallel-pair condition. It uses the boundary-cell lemma for the filtration of K, the new contractible-join theorem for each attached inclusion, and `def-coef-infinity-right-anodyne` for pushouts/transfinite composition. The attachment adds exactly the simplices whose nondegenerate initial ancestor is the newly attached simplex; characteristic-map identifications on faces are retained. A simplicial subset contains a degenerate simplex exactly when it contains its ancestor, by face retractions and degeneracies. Thus this specialization does not need HTT's additional degenerate-lift hypothesis for general noninjective diagrams. Empty support, the dangerous nearby false variant, is excluded by coverage.

Step 6 uses `lem-coef-infinity-anodyne-cocones`, whose statement supplies coherent cocone-space equivalences for every right-anodyne inclusion without assuming existing colimits, and explicitly supplies postcomposition compatibility. Combined with the dual cocone criterion in the cone-calculus node this makes the restricted cocone itself universal. Its apex is the chosen global colimit. This is stronger than an abstract agreement of homotopy classes and establishes the actual compatible comparison.

I opened each of these cited statements and checked that the quotations in citations.json occur verbatim. The cone-calculus quotation was expanded to cover its mapping-space invariance as well as its colimit criterion. The union of step uses equals proof_deps. Off-unit generic tools are declared only in split_report.tool_uses; the maintainer-owned tool_uses field is untouched.

For small cases I checked K empty (then H=N(I) and the final inclusion is an identity), I singleton (the ordinary cone construction), empty early K_i, two incomparable indices with a common successor, and an infinite directed union with no maximum. No finite-stage stabilization is invoked. For the join lemma, B a point gives the final horn case, A_0=A gives an identity, and A_0 empty with A a point gives B into its left cone; B empty is excluded by weak contractibility. For the comparison lemma, L empty gives both slices equal to E with singleton fixed-apex fibers; L a point gives the familiar coslice/arrow comparison. These checks preserve all source hypotheses and both variances.

## Validation and handoff

The initial server dry run printed `OK (not pushed)` with preflight passed. After the renewed recorded searches, explicit compatibility wording, strengthened citation quote and this report, the final dry run is rerun. No standalone checker was run on this machine. The two children remain unsplit, and independent second-reader review and delivery are still required.

## Second reading by Q11

- Step 1 checked against HTT Propositions 4.2.1.5, 4.2.1.7 and 4.2.3.4 and the quoted join-slice and cone-calculus statements; verdict: the fixed-apex representative and initiality argument is supported.
- Step 2 checked against HTT Lemma 4.2.3.3 and the statements of relative cone equivalence, terminal boundary extension, and trivial Kan fibration; verdict: the opposite-boundary calculation includes dimension zero and the stated hypotheses.
- Step 3 checked against HTT Notation 4.2.3.1 and Proposition 4.2.3.4 and the boundary-cell and join-slice statements; verdict: the mixed-subset filtration, successor attachments, limit unions, and transport paths are explicit and coherent.
- Step 4 checked against HTT Proposition 4.2.3.4 and Corollary 4.2.1.7 and the cited trivial-fibration, homotopy-equivalence, join-slice, and cone-calculus statements; verdict: the restriction map and fixed-apex cocone equivalences are established cell by cell.
- Step 5 checked against HTT Proposition 4.2.3.8 and Remark 4.2.3.9 and the filtered-nerve, boundary-cell, contractible-join, and right-anodyne statements; verdict: supports are nonempty directed, attachments are the displayed joins, and the transfinite right-anodyne closure applies.
- Step 6 checked against HTT Corollary 4.2.3.10 and the anodyne-cocone and cone-calculus statements; verdict: restriction gives the compatible colimiting cocone with the prescribed global apex.
- `lem-coef-join-slice-cocone-comparison` checked against HTT Propositions 4.2.1.5–4.2.1.8; verdict: self-contained statement-only auxiliary, with arbitrary simplicial shape and fixed-apex Kan fibers, not a restatement of the existing one-vertex slice nodes.
- `lem-coef-contractible-join-right-anodyne` checked against HTT Lemmas 4.2.3.5–4.2.3.6; verdict: self-contained statement-only auxiliary, with the exact monomorphism and weak-contractibility hypotheses and no extra Kan assumptions.

The second reading found no mathematical or citation repair. I confirmed that the item statement is unchanged from the base node, every citation quote is verbatim from its cited node, both new nodes have statement-only form with all definition dependencies and three-kind Mathlib searches, and the DAG has no cycle. I appended this section to satisfy the independent-review record; no node or proof text required alteration.
