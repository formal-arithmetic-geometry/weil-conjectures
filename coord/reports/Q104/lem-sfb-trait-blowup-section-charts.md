# Q104: lem-sfb-trait-blowup-section-charts

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-trait-blowup-section-charts.json`: statement, now split into seven proof steps. Statement and all inherited provenance and searches retained. No exact Mathlib match.
- `citations.json`: 38 verbatim statement quotations, covering every step/node citation.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. Every required non-elementary ingredient already has a node; the fraction calculations belong in the item itself.

## Attachments

None. I searched `lean/WeilConjectures/` for the item's blueprint tag, dilatation, uniformizer, and blowup terminology, and read the universal-property module `Blowup/BlowupUniversal.lean`. It contains general chart-ring and invertible-ideal lifting tools, but no declaration giving this item's full combination of flatness, section bijection and uniformizer-chart factorization. General existing blowup results are cited through the DAG rather than treated as an attachment for this item.

## Literature wanted

No additional source is needed for this split. The inherited source mentions BLR; its local scan is absent, so I do not claim to have read it. The proof here follows the available Stacks source instead, including the actual chart and fraction arguments.

## Corrections and blueprint comparison

The statement is unchanged and no statement dispute was found. The imported item had no proof. Its ordinary blowup is essential: replacing it by the uniformizer chart alone would lose sections whose reductions avoid the centre.

I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof, especially (3), together with the chapter and unit records and the immediate parent `lem-sfb-generic-smooth-model-smoothening`. This technical descendant supplies the special-fibre blowup step in the recorded smoothening/Neron-model ancestry; it does not replace a unit-level route. The ancestor command returns `None`, consistent with the item's inherited `blueprint.from.node = null`. I retain that result instead of inventing an imported ancestor, and specify the role of the item in `from.place` and `split_report.blueprint`. Whole-blueprint search for blowup found the general Nagata chart and complement nodes, which are reused; no blueprint node states this whole item. The chapter/unit metadata are retained.

The Stacks tag table matters here: 0804 is the affine chart lemma, 02OS is the complement/effective-Cartier lemma, and 0805 is flat base change. I corrected my initial draft source labels to these actual tags before delivery.

## Not duplicates

No new node is proposed. In particular, I reused the existing PID torsion-free flatness leaf, flat-module torsion-freeness leaf, finite-type algebra Noetherianity leaf, finite-type composition leaf, chart definitions and cover/isomorphism results, properness and complement results, valuative extension, and flat-pullback chart restrictions. The general space separated-composition theorem already covers scheme morphisms, so I did not create a duplicate scheme-only leaf even though Mathlib directly provides `AlgebraicGeometry.IsSeparated.instCompScheme` at `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean:75`.

## Review by Q104

I read Stacks `divisors.tex`, labels `lemma-blowing-up-affine` (0804), `lemma-blowing-up-gives-effective-Cartier-divisor` (02OS), `lemma-flat-base-change-blowing-up` (0805), `lemma-universal-property-blowing-up` (0806), `lemma-characterize-affine-blowup`, and `lemma-blowing-up-projective` (02NS). I also read `more-algebra.tex`, labels `lemma-flat-torsion-free` (0538), `lemma-valuation-ring-torsion-free-flat` (0539), `lemma-dedekind-torsion-free-flat` (0AUW); `algebra.tex`, `lemma-characterize-dvr` (00PD); `schemes.tex`, `lemma-separated-permanence` (01KU); and `morphisms.tex`, `lemma-finite-type-noetherian` (01T6), `lemma-composition-finite-type` (01T3), and `lemma-characterize-proper` (0BX5). There are no new nodes requiring separate source verification.

For step 1 I opened all seven cited nodes. The closed-immersion ideal statement gives quasi-coherence and the affine kernel; the DVR definition and the Noetherian-ring definition make R Noetherian because every ideal is principal. Finite type provides a finite cover by finite-type R-algebras, the algebra Noetherianity node applies to precisely these rings, and the quasi-coherent finite-type affine criterion makes the centre ideal of finite type. The proper-blowup statement requires exactly that hypothesis. I avoid assuming that an arbitrary closed centre has a finitely generated ideal without this check.

For step 2 I opened the proper-morphism definition, finite-type composition leaf and space separated-composition node. Properness supplies separatedness and finite type for b; the two composition clauses give those properties for the structural composite. The space theorem is used only for its separated-composition clause on schemes, which is the representable case of its definition. No finite presentation hypothesis is imported from its other clauses.

For step 3 I opened the local-model definition, chart-cover proposition, chart-isomorphism proposition and its chart-map definition, chart-ring definition, flat-morphism definition, flat-affine criterion, flat-domain-module torsion-free statement, localization definition, DVR definition and PID torsion-free flatness leaf. These give the actual subrings of B[1/a], not an unsaturated polynomial presentation that can retain torsion. B is torsion-free by flatness, but it need not be a domain. I wrote the localization equality calculation explicitly to prove that B[1/a], and therefore its chart submodule, is R-torsion-free even if a is a zero-divisor. The PID theorem needs no finite generation of that module. The affine-flat criterion and pointwise definition then prove global flatness. All chart hypotheses are established in step 1 and no irreducibility or reducedness is used.

For step 4 I opened the global complement theorem, centre-ideal definition and base-change definition. The complement isomorphism is exactly the cited statement. The generic fibre lies there because pi belongs to the centre ideal and becomes a unit in K. This does not require identifying K with a particular localization presentation.

For step 5 I opened the flat-domain-module statement, DVR definition, complement theorem and proper-separated valuative-extension statement. A is nonzero since it is a DVR; its flatness forces the image of pi to be nonzero. The DVR definition records its valuation-ring characterization, so the valuative node really applies with fraction field Frac(A). Properness and separatedness of b were established, the prescribed generic map exists by the complement isomorphism, and any candidate lift has that same generic restriction. Thus the uniqueness clause proves injectivity as well as the existence clause proving surjectivity.

For step 6 I opened the chart-ring and chart-map definitions, chart isomorphism and flat-pullback chart-restrictions node, plus the flat-morphism definition. The restriction node explicitly says that the inverse image of the a-chart is the chart of the extended ideal, and includes open immersions. Open immersions are flat directly on their local rings. Taking a=pi, included among generators, gives the required agreement; the localized-generator equality is written out and the maps agree on those generators. Thus the result is a glued open inside the existing blowup, not a separately postulated dilatation or a flat-base-change assertion used on the generally nonflat section map.

For step 7 I opened the centre-ideal statement, localization universal-property leaf, chart-ring definition, chart isomorphism, and valuative-extension statement. An affine containing the closed image contains the whole image of the local spectrum. Scheme-theoretic reduction into Z is precisely beta(I) contained in pi A, including when Z or the special fibre is nonreduced. I first map B[1/pi] to Frac(A), where pi is invertible, and then restrict the image to A by the generator calculation beta(i)/pi in A. This proves that all relations are respected without assuming a presentation for the chart. The resulting spectrum map is a lift into the chart; valuative uniqueness proves it is the previously constructed lift.

I checked B--E of the delivery errors against the statements and sources. No proof was transferred into a new clause-shaped node, no source is cited in place of a node, no definition is used to supply an unstated theorem, and every cited statement was opened. `citations.json` copies the actual node statements verbatim. All seven steps are below 2000 characters. The only elementary-marked step is restriction of the already cited complement isomorphism to the generic fibre. I preserved all inherited fields and added only split-owned proof/search/report metadata.

Small cases: if Z is empty, I=B, the blowup is X and its pi-chart is the generic open B[1/pi]; no A-point can reduce into the empty centre, so the factorization clause is vacuous. If Z=X_k, I=(pi), the pi-chart is B and the blowup is the identity. Empty X and empty affine charts cause no exception. For a flat nonreduced model such as R[epsilon]/(epsilon^2), B and its localizations remain torsion-free over R; the proof never cancels arbitrary elements of B. For disconnected X, the cover, chart and local-spectrum arguments apply on each image without choosing a global component. The maximal-ideal hypothesis pi A is used exactly to interpret reduction into Z as divisibility by pi; excellence and smoothness are unused.

## Unfinished work

None in the one-level stage-1 split. The existing dependencies retain their own states; no Lean was written and no compiler, Lake or build command was run.
