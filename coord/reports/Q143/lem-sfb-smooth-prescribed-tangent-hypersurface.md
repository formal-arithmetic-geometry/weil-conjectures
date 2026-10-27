# Q143 stage-1 delivery

Item: lem-sfb-smooth-prescribed-tangent-hypersurface. Date: 2026-10-24.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-prescribed-tangent-hypersurface.json: statement, now split into nine proof steps. Mathlib verdict: no exact match or one-line specialization. No statement or statement-dependency changes.
- citations.json: one verbatim statement quotation for every step/node pair.
- report.md: this report. searches.jsonl contains the actual Q143 searches. write_split.py is sandbox-only preparation material.

New nodes: 0. New Mathlib leaves: 0. All substantive tools already have nodes.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and the notions prescribed tangent, tangent hyperplane, hypersurface and smooth pointed curve. The hypersurface declarations found concern generic function-field models or formal fibres, not this statement. In particular there is no project theorem asserting the required prescribed tangent germ to attach.

## Literature wanted

None.

## Findings and corrections

The item was unsplit, with no earlier sandbox split or report. There is no repair note for it. Its statement is correct and is retained exactly. Milne, Abelian Varieties, Chapter I Lemma 3.6, printed p.18, explicitly takes an ambient hyperplane transverse at the point and its unique component through that point. Here the prescribed hyperplane lies in the tangent space rather than the ambient affine space; the cotangent-class construction makes that linear choice precise without requiring a fixed embedding. The proof is recorded as agent-written, since the detailed local algebra, ambient shrinking and geometric-integrality assembly are supplied here.

The recorded chapter/unit and historical ancestry are retained. tools/blueprint_refs.py ancestor reports blueprint.from.node = None for this already-created historical branch, and its existing from.place explains why the current direct-image blueprint no longer contains that auxiliary Picard argument. I read the latest blueprint and searched the entire imported blueprint with blueprint_refs.py search for tangent, hypersurface and regular local. There is no blueprint node stating this item; same_as remains empty. I do not manufacture an ancestor or alter the unit's route or realized fields. This is not a key node of the unit.

I searched the whole DAG by the item's source tags and by tangent/cotangent duality, regular quotients, smooth neighbourhoods, dimensions, components and geometric integrality. This found every required non-elementary tool. In particular the regular-parameter theorem gives both regularity and the exact dimension drop, the regular/separable affine-neighbourhood lemma gives a principal smooth open, the smooth-components node gives the component separation, and the finite-field-extension test gives geometric integrality. No subordinate node that would repeat a clause of this item is introduced.

During checking I replaced an unnecessary appeal to Noetherian restrictions of arbitrary affine opens with the finite-type affine cover supplied directly by the definition. I also made the affine fibre-product citation explicit in the diagonal and scalar-extension steps and corrected the diagonal source pointer to Stacks Tag 01I4 (an initial draft had the unrelated 01L7). Most importantly, the proof shrinks the ambient affine scheme twice along lifts of functions on the zero scheme; it never treats an arbitrary open in a closed subscheme as automatically closed in the original ambient scheme.

## Unfinished work

None in the stage-1 split. No Lean was written or compiled. Mathematical review by the maintainer remains the next independent review after delivery.

## Not duplicates

No new nodes. Existing statements are cited directly, including off-unit tool statements; their use is declared in split_report.tool_uses.

## Review by Q143

I read Milne I.3.6 on printed p.18 and the actual Stacks statements in algebra.tex for Tags 00NQ (lemma-regular-ring-CM), 00TV (lemma-separable-smooth), 00OS (lemma-dimension-spell-it-out), and 0FWF (lemma-characterize-geometrically-integral); in varieties.tex I read Tags 0B2E/0B2F for tangent spaces and tangent maps, 0A21 for dimensions of integral opens, and 056S for smooth regularity; in schemes.tex I read 01I3 and 01I4 for principal opens and affine fibre products. I also read the normal-component discussion in properties.tex. There are no new-node sources to check. I opened each cited DAG statement, rather than using anything available only inside its proof.

Step 1 uses the finite-type definition and lem-pc-affine-finite-type-algebra for the chart; the geometric-integrality and integral-scheme definitions for its domain property; affine-open-stalk-localization for its local ring; smooth-scheme-over-field-regular for regularity; and the finite-type-domain maximal-localization, spectrum-dimension and integral-open-dimension nodes for dim R = d. The chart is nonempty because it contains p; its evaluation kernel is maximal because evaluation is onto k, so the maximal-localization hypothesis is met.

Step 2 uses regular-local-cotangent-dimension for finite dimension and rational-point-tangent-derivation-identification for the actual isomorphism with the dual. The class is constructed by an explicit basis double-dual calculation; codimension one is exactly what ensures a nonzero functional with kernel H. Step 3 uses the full fraction representation in affine-open-stalk-localization and the principal-localization-open-immersion node. Its denominator avoids p, and vanishing of the residue makes the numerator belong to the maximal ideal. No equation is chosen merely up to an untracked tangent-space isomorphism.

Step 4 uses Nakayama on the finitely generated maximal ideal of a Noetherian regular local ring, and the regular-local-generators-regular-sequence node with c=1. Its statement explicitly gives the quotient's regularity and dimension d-1; a node saying only regularity would not suffice. Step 5 uses zero-scheme-properties for the actual affine quotient, localization-at-prime-of-quotient for the local ring and its quotient map, regular-separable-affine-smooth-neighbourhood for a principal smooth open, and localization-quotient-commute for lifting that open to the ambient scheme. The residue field is k itself, hence is a finite separable extension of k, exactly as the smooth-neighbourhood node assumes; no unsupported regular-over-an-imperfect-field implication occurs.

Step 6 uses smooth-components-disjoint only on an affine finite-type smooth scheme, where all its hypotheses hold. A principal open inside the component is chosen by the explicit Zariski basis argument. The principal-open and localization/quotient nodes give the actual ambient closed zero scheme. Smooth-restrict-open-subschemes supplies smoothness, smooth-scheme-over-field-regular supplies every regular stalk, and regular-local-domain supplies domains. Reducedness follows by checking nilpotents in all stalks; the integral-scheme definition then combines reducedness and irreducibility. This proves integrality without assuming that the full zero scheme is irreducible.

Step 7 checks finite generation by listing the inverse generators introduced by localization. Its separatedness argument uses fibre-product-affine-spectra to describe the diagonal and the closed-immersion definition for the surjective multiplication map. It uses the same two exact dimension nodes as step 1, now on the integral coordinate ring of D and its k-rational maximal ideal. Step 8 uses rational-tangent-cotangent-duality, whose statement includes naturality with the local-ring map. The proof explicitly computes the quotient E/kv and its dual image, so the tangent subspace is exactly H; it does not just compare dimensions. Step 9 uses geometric-integrality-finite-field-test with the coordinate domain of D: every finite extension of the algebraically closed k is isomorphic to k. Fibre-product-affine-spectra identifies the resulting scalar extensions with the required base changes, and the geometric-integrality definition gives the asserted conclusion.

For small cases I checked Y = affine d-space at the origin and H given by x_1 = 0, which yields the usual affine hyperplane with dimension d-1; d=2 gives a smooth pointed curve. A function with nonzero linear term can have additional components away from p (for example x_1(x_1-1)); the explicit component shrinking removes them. In characteristic p, x_1^p has zero cotangent class and is excluded by the constructed nonzero v, so it cannot cause a nonreduced cut. All localizations invert elements nonzero at p, retaining the point and its residue field. No step exceeds 2000 characters. I checked delivery-errors B--E: no new unsplit node or hidden clause-node, all object types and hypotheses accounted for, no weakening, no SGA source, no unsupported tag-only fact, and every cited statement is quoted verbatim in citations.json.

The actual Q143 leanfinder, leansearch, loogle and two grep searches are logged in searches.jsonl. I read their hits. The smooth-locus localization declarations only provide a tool after smoothness at a prime has been established; manifold tangent-space hits have different objects. The source hit Algebra.IsSmoothAt.exists_notMem_smooth was read at Mathlib/RingTheory/Smooth/Locus.lean:150, and the FormallyUnramified cotangent hits were read at Morphisms/FormallyUnramified.lean:105. Neither proves this item. The two semantic phrasings and two source directories gave no exact theorem.
