## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-profinite-coefficient-inverse-image.json: statement, split; no Mathlib match found.
- citations.json: one verbatim statement quote for each citation in the eight proof steps.

No new nodes, no Mathlib leaves. The unit is not changed: this is a supporting coefficient lemma, not its key statement.

## Attachments

None. Searches of WeilConjectures in the read-only slopmaster2 source by the item's blueprint tag, profinite coefficients and constant-sheaf pullback found no declaration stating this arbitrary finite-ring-tower result. Adic/UpperStar.lean:310 gives upperStarAdicConstantSheafIso for the specific Qbar_l-valued adic sheaf, not all countable towers of finite commutative rings. It is not an attachment. Upstream master's ModuleObject proper-base-change theorem uses condensed coefficients p_X^* E and remains sorried; it is not evidence for this ordinary ring-sheaf tower result.

## WANTED

None.

## Corrections and scope

The item's statement is retained verbatim. Its original proof was empty. Inverse image need not preserve arbitrary infinite limits: no such general claim is used. Its preservation here follows because the coefficient tower limit is itself represented by an object of the pro-etale site. No surjectivity of the ring transitions, Noetherianity, connectedness, properness, finite type, or restriction on the scheme morphism is required.

The proof_origin is agent: the argument assembles the cited source results and is not falsely attributed to a single Stacks theorem. The blueprint ancestry remains def-weil-pbc-four-corners, at its coefficient-identification clause. Searches of the whole blueprint for profinite and constant sheaf found no second node stating the joint finite/profinite comparison with the specified projection and coherence clauses; same_as is empty. The generic site, descent, limit and Yoneda results from other units are declared as tool uses; they do not replace a proper-base-change unit step.

## Unfinished work

None in this one-level split. Existing cited nodes retain their own proof status. No Lean was written and no compiler or build command was run.

## Not duplicates

No new nodes. Reused the existing fpqc representable descent, scheme coproduct, inverse-image definition, affine-transition limit, ind-etale stability, general Yoneda evaluation and coyoneda uniqueness nodes. In particular lem-galois-inverse-image-representable only states an etale result: it was read but is NOT cited for the pro-etale assertion. Likewise the topological-space inverse-image node is not used for a scheme site. The actual pro-etale representable comparison is proved by the adjunction and the general Yoneda nodes in step 5.

## Review by NC

I read proetale.tex Tag 098T, label lemma-morphism-big-small, especially (2) and its proof: the functor is base change, and its direct image really is evaluation at the base-changed object. I read Tag 097N, label lemma-ind-etale-implies: it says ind-etale algebras are weakly etale. I read sites.tex Tag 04D3, label lemma-pullback-representable-sheaf, and its adjunction route, Limits 01YW/01YX at lemma-directed-inverse-system-affine-schemes-has-limit and lemma-directed-inverse-system-has-limit, Descent 023Q at lemma-fpqc-universal-effective-epimorphisms, Sites 0H7J at example-constant-sheaf and 00WJ at lemma-sheafification-exact, and Sites Modules 03CO at lemma-limits-colimits-abelian-sheaves. These are assembled sources; none by itself claims the whole item. There are no new-node sources to review.

Step 1 uses the site's fpqc covering convention and the full statement of fpqc-representable-descent. That statement glues scheme morphisms to any scheme, and uniqueness applied again to the base proves the glued morphism is over T. It does not assume T affine. This establishes the sheaf property required later for actual site objects, rather than citing a definition for subcanonicity.

Step 2 uses scheme-coproduct-family for existence and the disjoint open copies, and the constant-sheaf and sheafification definitions for their universal property. The partition-to-section gluing argument proves that universal property explicitly, also for ring values by refinement of two partitions. The proetale-covering and weakly-etale definitions justify the partition cover. I replaced a compressed assertion about clopen affine intersections with the explicit finite principal-open subcover argument: on an affine, the basic opens covering it generate the unit ideal, so finitely many suffice. The locally constant functions factor through the connected-components quotient; finite-discrete continuity gives exactly these clopen partitions. This is an elementary step from those definitions and the coproduct statement, not an invocation of the finite-constant comparison clause being proved.

Step 3 uses limit-affine-transition for existence and restriction of the limit and its explicit affine coordinate-ring formula. It is a directed countable index and all transitions are affine, because inverse images of affine opens are finite disjoint copies. The definition of ind-etale and the statement of ind-etale-stability give weak etaleness of the affine restriction. Etaleness of B^{Q_n} is checked on its copies, where the map is the identity; the etale definition has exactly finite presentation, flatness and open diagonal. Flatness with flat diagonal is local on these affine charts, so the weakly-etale definition proves site membership globally. The universe bound is preserved under this countable construction, rather than treating a large indexing category as small. The finite union of affine copies has ring B^{Q_n}: the projections of a finite product give disjoint basic opens on its spectrum, each the original affine, so this elementary coordinate description applies also to transition maps that merge labels.

Step 4 uses def-pur-sheaf-inverse-limit, whose statement expressly includes ring sheaves and sectionwise compatible tuples, not merely modules. Its projections match the scheme-limit projections by the universal property. Ring-object equivalence gives the intended interpretation; operations are constructed coordinatewise, and their identities are checked coordinatewise. This is elementary from the stated limit properties.

Step 5 uses inverse-image for the adjunction and precise direct-image formula, yoneda-hom-bijection for evaluation (NOT just a full-faithfulness node), and coyoneda-iso-of-natural-hom-bijection for the unique isomorphism. Both source and target representables are sheaves by step 1 and are site objects by step 3. The Yoneda statement includes naturality in objects and in presheaves. Evaluation at the identity explicitly determines the adjunct as base change, which is needed to identify the canonical comparison.

Step 6 is the fibre-product/limit universal-property calculation written out with an arbitrary test U-scheme. It proves base change of E_V is E_U without commuting the topos inverse image with infinite limits. This step uses only def-pc-fibre-product and the preceding constructed limits and comparisons. No transition surjectivity enters it.

Step 7 uses presheaf-pullback-sets-left-exact with the small site categories and the finite-limit-preserving base-change functor from inverse-image, then sheafification-sets-exact to get finite-product preservation for sheaf inverse image. Sheaf-algebraic-structures-objects states the ring-object/ring-sheaf identification and the criterion on operations. The adjunction restricts to operation-preserving maps by naturality of the product-compatible unit and counit; this shows these ring structures are the ring inverse image in the statement. The representable comparison preserves products by its evaluation formula, hence each operation by naturality. The prescribed finite adjunct is explicitly the same-label map on constant sections. This checks the coefficient category rather than silently using an abelian-only underlying-sheaf theorem for rings.

Step 8 checks the two equations on the actual projections and label transitions. For a morphism of towers, the finite diagrams commute by naturality and the infinite diagram commutes after each projection; uniqueness in the limit makes the maps equal. For composition, the two adjuncts base-change the same map once or twice, and the fibre-product uniqueness makes them the same under association. The infinite-level composition follows again from its projections. These are explicit elementary uniqueness arguments with the inverse-image adjunct and fibre-product definitions, not an unexplained assertion that coherence transports.

I tested the singleton zero ring (one copy of T, so the zero-ring sheaf, with no empty-set-of-labels mistake), empty schemes (all section values are the unique empty-domain sections), constant towers (E_T is the finite disjoint union itself), and towers with non-surjective unital maps. A constant tower with an idempotent endomorphism projects onto its compatible labels, and the affine-colimit construction still gives the right limit; no lifting of labels is assumed. Disconnected and non-affine bases are handled by partitions and affine restriction, without assuming global sections are constant or the base affine. I checked B1–B10 and C1–C8: there are no new unsplit proof sketches or duplicate nodes, every cited statement has been opened and quoted in citations.json, and all non-elementary tools occur in uses. D1–D5 are addressed by the actual construction in steps 2–6 and explicit ring/coherence argument in steps 7–8. E1–E7 are addressed by the hypothesis and small-case checks above. No statement dispute or source error was found.

## Second reading by NC

- Item statement: checked against the coefficient-identification clause of `def-weil-pbc-four-corners` and the stated pro-etale definitions; all hypotheses (arbitrary scheme morphism, countable finite unital ring tower, universe bounds) and all projection, transition, naturality, identity, and composition clauses are present.
- Step 1: checked against `lem-weil-pbc-fpqc-representable-descent` (Tag 023Q) and the pro-etale covering definition; descent gives representable sheaves and the over-the-base condition by uniqueness.
- Step 2: checked against `lem-weil-pbc-scheme-coproduct-family`, constant-sheaf/sheafification definitions, and the covering and weakly-etale definitions; the finite clopen partition and finite affine refinement argument supplies the universal property, including ring operations.
- Step 3: checked against `lem-weil-pbc-limit-affine-transition` (Tags 01YW/01YX), the ind-etale algebra and stability statements, and etale/weakly-etale definitions; finite products are etale, the filtered colimit is ind-etale and therefore weakly etale, and the affine limit is in the chosen universe.
- Step 4: checked against `def-pur-sheaf-inverse-limit` and `lem-weil-pbc-sheaf-algebraic-structures-objects`; sectionwise compatible tuples and coordinatewise operations give the represented inverse-limit ring sheaf.
- Step 5: checked against `def-weil-proetale-inverse-image`, `lem-galois-yoneda-hom-bijection`, and the coyoneda uniqueness lemma; the adjunction identifies inverse images of representables with base-changed representables and identifies the adjunct on identities.
- Step 6: checked directly against `def-pc-fibre-product` and the limit universal property; the test-object calculation proves both finite and infinite base-change identifications without assuming inverse image preserves arbitrary limits.
- Step 7: checked against the left-exact presheaf pullback, exact sheafification, ring-object, and inverse-image statements; finite products and all five ring operations are preserved, and the prescribed constant-section adjunct is recovered.
- Step 8: checked against fibre-product functoriality, inverse-image adjunction, and uniqueness of limits; projection/transition equations, tower naturality, identity, and composition follow after each coordinate projection.
- New nodes: none; all cited nodes were searched in `dag/nodes/` and their statements were opened. No Mathlib leaf was needed; the recorded LeanFinder/Loogle/LeanSearch/grep searches found no exact theorem.
- Changes made: corrected the node metadata `created.item` to the delivered item (the worker had left the blueprint ancestor), and replaced the non-verbatim `def-weil-pbc-ind-etale-algebra` citation quote with the node's exact statement. Dry-run preflight and citation checks now pass.
- Small cases checked: singleton/zero ring, empty schemes, constant towers, non-surjective transitions, disconnected and non-affine bases; no statement or hypothesis fault found.
