# Stage-1 delivery: lem-sfb-space-unramified-diagonal-open

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-unramified-diagonal-open.json: statement, split in six steps, no Mathlib match for arbitrary algebraic spaces.
- citations.json: one verbatim statement quotation for each citation in each proof step.
- searches.jsonl: five actual searches for the item (LeanSearch, Loogle, two LeanFinder phrasings, Mathlib grep).
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The sandbox initially had only launcher brief markers; there was no earlier item, proof, report or search log to overwrite.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for unramified/diagonal terminology. The source module WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean defines an equality locus only for schemes. It cannot attach this item for arbitrary algebraic spaces. Mathlib's AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal, read at Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean:126, likewise has scheme objects. All search services returned answers; none was recorded as an absence while unavailable.

## Wanted literature

None. All mathematical sources used are present in literature/stacks-project/.

## Corrections and scope

The statement is mathematically correct: Tag 05W1(1) requires neither representability of g nor separation, quasi-compactness or Noetherian assumptions. The original item had no proof. I corrected doubled literal TeX backslashes in the statement to single TeX backslashes; the mathematical hypotheses and conclusion are unchanged. No statement dispute, source error, new notion or new node was necessary.

The latest blueprint was read via literature/blueprint/latest/: sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, together with the chapter and unit records. The item is a generic geometric prerequisite below the inherited direct-image provenance. Its inherited blueprint.from.node is null, as tools/blueprint_refs.py ancestor reports. I retained that provenance and the existing via list rather than invent an ancestor. Whole-blueprint searches for 'unramified diagonal', '05W1', and 'open diagonal' returned no imported blueprint node with this statement.

## Not duplicates

No new nodes were created. The existing lem-sfb-unramified-space-open-diagonal is the forward assertion only for a scheme target; this item allows arbitrary algebraic-space targets. The existing lem-sfb-space-unramified-open-diagonal is the reverse implication, assuming local finite type and an open diagonal. The existing lem-sfb-space-etale-monomorphism-open is the general etale-monomorphism criterion, not the unramified-diagonal assertion. I read these statements and reused the underlying existing chart calculus and scheme criterion without cloning any of them.

## Review by NO

I read spaces-morphisms.tex Tag 05W1 (lemma-diagonal-unramified-morphism), including its displayed diagram and its proof of part (1). My six steps follow that diagram. I also read spaces-properties.tex Tag 03EC (lemma-etale-over-space), including the scheme comparison clause (2); descent.tex Tag 036W (lemma-etale-etale-local-source); morphisms.tex Tags 02GE (lemma-diagonal-unramified-morphism) and 02GP (lemma-open-immersion-etale); and etale.tex Tag 025G (theorem-etale-radicial-open), especially (3) implies (1). I used Stacks directly, with no SGA source. No new node needs an additional literature review.

For step 1, def-trf-algebraic-space explicitly requires a representable absolute diagonal. Pulling it back along the two maps from T represents W as a scheme. The monomorphism proof is written on all test-scheme sections; it does not confuse injectivity on field-valued points with a monomorphism. The target product is the relative product over Y, and the equality condition makes its diagonal pullback the same scheme as the absolute-diagonal pullback over S.

For step 2, I checked the full statement of lem-sfb-unramified-etale-compatible-charts: it supplies the compatible source atlas for the chosen surjective target atlas, and the all-compatible-charts unramified condition applies to h. The open diagonal then follows from the actual definition in def-weil-unramified-morphism, not from an unstated theorem. Clause (1) of lem-weil-pbc-etale-composition-cancellation explicitly makes an open immersion etale. The atlas existence clause used here is in def-trf-algebraic-space.

For step 3, lem-trf-space-fibre-products-etale-covers says the sheaf products are algebraic spaces. I checked lem-trf-space-representable-etale-scheme-tests supplies all three required extra statements: scheme representation when both sources are schemes, permanence under composition and arbitrary space base change, and etaleness of a comparison between two etale scheme charts. Thus V and R are schemes etale over Y when its comparison clause is applied. The coordinate proof of D = Q times_R V inserts or forgets the forced V coordinate and works on every test scheme. It uses the same relative base Y throughout. I explicitly did not infer surjectivity of the middle arrow D to P: it need not hold.

For step 4, the same scheme-tests node gives schemes E and F and all their etale base-change/composition properties. The two displayed pullback identifications are proved by inverse natural operations on sections, not by a claim of containment of point images. The map F to W is specifically the base change of the surjective etale atlas a. I read lem-trf-etale-descent-through-source-cover: its three schemes are exactly (T,W,F), its cover is F to W, and its composite is F to T, already verified etale. It requires no quasi-compactness of the cover and no separation or finiteness of the schemes.

For step 5, def-weil-etale-morphism actually gives both flatness and local finite presentation. I checked these match lem-pe-flat-lfp-monomorphism-open, and that step 1 supplies the latter's functorial monomorphism hypothesis. The lemma concludes an open immersion of schemes, including the structure sheaf, not merely an open point map. Its application is repeated for arbitrary T to P, exactly the requested representable conclusion.

For step 6, def-a1-space-open-subspace defines an open subspace as a subfunctor whose scheme pullbacks are open immersions. The image of the diagonal is a subfunctor isomorphic to X by either projection, so it is already a sheaf. Its pullback along T to P is the scheme W proved open in step 5. This supplies the open subspace J without assuming an unproved topological image theorem.

I verified every cited node is unmerged, read each cited statement, and wrote citations.json with literal substrings of those statements. A traversal of statement and proof dependency edges found no path from any used node back to this item. Each proof step has fewer than 2000 characters, with the coordinate identifications spelled out. The off-unit uses declared in split_report.tool_uses are the existing generic fibre-product, representable-etale calculus and scheme source-descent tools; they do not replace a step of the unit route. Scheme definitions and the Mathlib open-monomorphism criterion need no route exception.

I tested empty X and empty atlases (the empty surjective etale cover of the empty scheme is allowed), identity morphisms (W=T and J=P), open immersions (diagonal is an isomorphism), and a finite etale cover of degree two (the off-diagonal component is excluded by J). None of the constructions assumes reduced test schemes, a scheme target, a surjective middle arrow, separated atlases, affine intersections or a Noetherian base. No additional hypotheses were introduced.

## Unfinished work

None within this one-level stage-1 split. Existing dependencies retain their own states and are not modified.
