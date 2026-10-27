# Stage-1 report: lem-sfb-nodal-branch-double-cover

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-branch-double-cover.json: split, with an intrinsic graph-conormal construction, nodal-chart calculation, arbitrary-base-change comparison, fibre normalization identification and finiteness argument. Its statement is unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-augmented-etale-associated-graded.json: statement only, unsplit; no Mathlib match for the isomorphisms of all ideal-power quotients and the associated graded algebra.
- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-local-tangent-normalization.json: statement only, unsplit; no Mathlib match for the local quadratic normalization-residue/tangent-Proj identification.
- citations.json: one verbatim statement quotation for every use in every item proof step.
- searches.jsonl and search-results.txt preserve the actual search records and results. search-plan.json names the intended nodes for each search. A candidate descent node was searched but not created after exact existing descent nodes were located.

Two new nodes, zero Mathlib leaves. No Lean files or unit/chapter records written. All work is confined to the assigned sandbox.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag and for nodal, branchCover and normalization-branch terminology. The hits were comments, unrelated nodal counterexamples, and Nagata normalization finiteness; none states this relative branch-cover assertion. The item has no finished declaration to attach.

## Sources wanted

None. All mathematical sources used here are present in literature/stacks-project/.

## Corrections and scope

The imported item had no proof. I retained its statement and its graph ancestry, source record, chapter and unit. The ancestor search reports blueprint.from.node = None, as already recorded on the item; the source place still identifies det-thm-sf-ctf-stability-direct-images (3), the ILO/de Jong nodal quasi-splitting subargument. The whole-blueprint searches for nodal, conormal, quadratic, tangent, infinitesimal, graded, finite etale and finite locally free found no equivalent branch-cover theorem or either of the new local algebra lemmas. The unit and chapter records were read; this is a tool construction below the direct-image alteration route, not a modification of that route, and this item is not a unit's key statement.

The important implementation distinction is between the normal cone of the graph AFTER base changing X to D and the normal cone of D in X. They are different in a smoothing uv=h. The latter would lose the two branches when D has codimension two or when h is a smoothing parameter. The proof constructs the former on affine graph neighbourhoods. It also avoids treating the global graph as closed: f is not assumed separated. Only graphs with affine source and affine base are used, and these give canonically identical germs on overlaps.

I did not use normalization of the total family, nor assert that it commutes with arbitrary base change. Only the normalization of an individual fibre enters the local algebra lemma. The local equivalence of the tangent-Proj description and the normalization-residue description is explicitly omitted in Stacks 0CBT; that genuine local algebra result is a new unsplit dependency rather than a hidden inference.

## What remains

The split is complete by one level. Both new algebra lemmas remain statement-only work for the queue. No construction or proof has been represented as a completed Lean proof. The original item is neither disputed nor weakened.

## Review by NX

I read Curves 0CBY (lemma-etale-local-structure-nodal-family), including the arbitrary-base Noetherian-approximation paragraph, and 0CBT (remark-quadratic-extension), 0CBU (remark-trivial-quadratic-extension), and 0CBW (lemma-split-node). For the new infinitesimal lemma I read Algebra 0H1D (lemma-formally-etale-lift-infinitesimal), its inductive proof, and 00UR (lemma-formally-etale-etale). For the new local tangent-normalization lemma I read all three constructions and the final scheme-fibre sentence of 0CBT; it is precisely the local comparison, including the source's omitted equivalence, that is postponed. I read the conormal-algebra construction and functorial comparison in Divisors 0630-0635 and Fitting base change in 0C3I. For descent I read Descent 02VN and 02VO, including fixed degree in the latter. Sources for existing nodes were compared with their actual statements, not inferred from titles.

Step 1 uses lem-trf-nodal-family-fitting-singular for the unramified singular scheme, its support and arbitrary base change; its hypotheses coincide verbatim with this item's. lem-trf-unramified-field-fibre-decomposition states the unrestricted disjoint union of finite separable spectra, so reducedness does not require a finite-type or proper hypothesis here.

Step 2 takes the actual graded ideal-power quotients, affine identifications and quasi-coherence from lem-pur-conormal-graded-algebra. The graph ring map is visibly surjective, so this node is applied to closed immersions as required. lem-weil-pbc-site-module-sheaf-gluing is applied to the Zariski covering and each degree, not to an unspecified descent problem; products and units agree on restrictions and are glued by the ordinary sheaf condition. Intersections are refined by affine opens, never assumed affine. Step 3 uses lemma-nagata-relative-proj-exists for existence and affine compatibility; def-nagata-relative-proj supplies the construction's meaning only.

Step 4 uses the exact etale-to-standard-model conclusion of lem-trf-nodal-family-etale-local-model. It writes the universal derivation calculation v du+u dv=0, rather than citing a definition for a Jacobian theorem. For the etale source comparison, lem-weil-pbc-flat-unramified-formally-etale provides unique lifts to the affine square-zero algebra B plus M; this gives unique extensions of derivations. lem-trf-fitting-ideal-independence-base-change states precisely the arbitrary tensor-base-change formula used to pull the Fitting ideal. Thus D_U is the scheme-theoretic preimage of u=v=0, not merely its set of points.

Step 5 applies lem-pur-conormal-algebra-flat-base-change only to the flat etale base change of the graph. The new 0H1D lemma applies to an etale ring map with surjective quotient onto the graph ring: it does not require the graph ideal to equal the extended old ideal. This distinction is why the new lemma is needed instead of misusing the existing flat-Cartesian conormal lemma. The monomial basis in A[u,v]/(uv) computes the whole graded algebra over arbitrary A, including rings with nilpotents and characteristic two.

Step 6 computes both degree-zero homogeneous localizations and their empty intersection. The existing degree-descent node has exactly an arbitrary jointly surjective etale family as hypothesis; the fpqc-finer-than-etale and fpqc-descend-etale nodes cover the separate etaleness assertion. lem-pc-flf-properties explicitly identifies the direct-image rank. The new descent node I initially searched for would have duplicated these statements and was not created.

Step 7 uses the SURJECTIVITY clause of lem-pur-conormal-algebra-flat-base-change for arbitrary, possibly nonflat base change. It does not use that lemma's flat-isomorphism conclusion. prop-nagata-relative-proj-functoriality supplies the closed immersion from a graded surjection, while lemma-nagata-relative-proj-base-change-arbitrary supplies the unrestricted Proj pullback. I checked the coefficient map on the monomial bases, so there is no assumption that ideal powers always commute with nonflat base change. lem-weil-pbc-etale-covering-base-change supplies the pulled chart covering. lem-weil-pbc-fpqc-descend-isomorphism has a single quasi-compact covering hypothesis, satisfied after a finite affine refinement over each affine base open; its use is on the corresponding cover of the comparison's target. Step 8 verifies the canonical comparison maps under composition on actual representatives, and is the sole elementary step.

Step 9 identifies the graph cone over each residue field with the local tangent cone. The finite separable residue extension comes from Step 1. lem-weil-pbc-finite-separable-extension-etale and lem-weil-pbc-etale-covering-base-change justify the etale scalar extension. Formal etaleness after localization is checked by the explicit lifting of units across square-zero ideals. Then 0H1D applies with inverse-image ideal equal to the maximal ideal. The new local lemma gives BOTH the tangent-Proj comparison and its normalization-fibre interpretation, so the proof does not misuse a definition of normalization for a localization theorem. Its geometric-node and residue-separability hypotheses were checked. The comparisons assemble over the disjoint open residue-field points, without assuming there are finitely many.

Step 10 uses finite presentation only for quasi-compactness, and closed-in-quasi-compact for D_t. A quasi-compact disjoint union of open points is finite. The separate field-spectrum etaleness node and separable-transitivity node state exactly the facts used for B_t; finite composition gives the finite-morphism assertion. Step 11 uses the actual closed-immersion-proper statement, the definition of quasi-finite (finite type plus isolated fibre points), proper-quasi-finite finiteness, and finite composition. Properness includes finite type, so no hidden finiteness assumption on T is introduced.

I tested the empty family and smooth family (D and B empty), the split node uv=0 over an arbitrary ring, a nonsplit real node with conjugate tangent directions (the quadratic algebra is C, not two arbitrarily ordered real points), characteristic two with separable quadratic tangent algebra, and a smoothing uv=h. In particular, base change of uv=epsilon over k[epsilon]/epsilon^2 to a base on which epsilon vanishes leaves a nonreduced singular base and still gives two copies of that base: the monomial calculation preserves those nilpotents. Infinite disjoint unions of nodes illustrate why fibre finiteness is claimed only under finite presentation. A nonseparated affine-chart gluing does not require a closed global graph. For 0H1D, localization away from an element invertible modulo I and an etale algebra with extra components away from the graph both give the same finite infinitesimal quotients; no J=IC hypothesis was smuggled in.

B1-B10: both new files are self-contained statements only, their notions are defined inline or have definition dependencies, their TeX uses single logical backslashes, the labels match the Stacks tags, and all recorded searches actually ran. The hits were read: formally-etale square-zero Hom lifting is insufficient to be a one-line match for all ideal-power quotient and graded-algebra isomorphisms; normalizationDesc and the relative normalization universal maps do not state the nodal tangent-cone theorem. There are no new Mathlib leaves. Blueprint references and the no-attachment check were completed. C1-C8: every imported fact is a cited statement with a verbatim quotation in citations.json, new claims have strictly smaller scope than the family theorem, and off-unit tools are declared in split_report.tool_uses for the maintainer. D1-D5: the item carries the construction and the calculation; neither new node constructs a family cover or states all its clauses. E1-E7: the hypotheses and small cases above were checked, no false source statement was reproduced, and no SGA source was used. Every proof step is below 2000 characters.

## Not duplicates

lem-sfb-nodal-local-tangent-normalization vs lem-trf-stacks-nodal-closed-subcurve: The new node identifies the projectivized associated graded local ring with the normalization residue algebra over the possibly nonclosed residue field. The existing node concerns inheritance of split nodal singularities by closed subcurves and the finite smooth intersection with the complementary subcurve. It gives no tangent-Proj or normalization-residue identification.

lem-sfb-nodal-local-tangent-normalization vs lem-trf-nodal-point-finite-separable-splitting: The new node identifies the projectivized associated graded local ring with the normalization residue algebra. The existing node supplies finite separable splitting of a node, not the tangent-Proj/normalization-residue isomorphism.

lem-sfb-nodal-local-tangent-normalization vs lem-trf-nodal-curve-normalization-euler: The new node identifies the projectivized associated graded local ring with the normalization residue algebra over the possibly nonclosed residue field. The existing node is the Euler-characteristic formula for a proper nodal curve over an algebraically closed field. It gives no isomorphism between the tangent Proj and the normalization fibre.

lem-sfb-nodal-local-tangent-normalization vs lem-trf-nodal-normalization-quotient: The new node identifies the projectivized associated graded local ring with the normalization residue algebra over the possibly nonclosed residue field. The existing node is a structure-sheaf normalization exact sequence for a proper nodal curve over an algebraically closed field. It does not identify the tangent Proj with the normalization residue algebra.

lem-sfb-nodal-local-tangent-normalization vs lem-sfb-nodal-branch-double-cover: The new node identifies the projectivized associated graded local ring with the normalization residue algebra. The existing item is the relative family cover, constructed and calculated in the item proof; it does not state this local algebra identification.

No matching source tags were found for 0H1D itself. Existing conormal flat base change (0635) requires a Cartesian centre and flat ambient map; the new formal-etale quotient lemma does not require a Cartesian centre. Existing degree/etaleness descent and Proj-base-change nodes were reused.

## Validation

The first required deliver.py --no-push completed successfully: preflight passed at dry-run commit 0e5ceb7d7b9. The final dry run includes the clarified duplicate comparisons and the explicit application of the derivation comparison to both etale maps in the nodal chart. No mathematical statement changed.
