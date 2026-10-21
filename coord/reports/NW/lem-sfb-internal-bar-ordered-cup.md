# NW — lem-sfb-internal-bar-ordered-cup

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-internal-bar-ordered-cup.json: item, six proof steps, statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-internal-bar-roof-adjunction.json: statement-only structural lemma, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-internal-inflation-graded-cup.json: statement-only structural lemma, unsplit, no Mathlib match.
- citations.json: every proof-step citation quotes the full actual statement so all clauses used are visible.

## Attachments

None. Searched WeilConjectures and Sheaf for the exact blueprint tag and for internal bars, ordered cups, character cups and Alexander–Whitney. The discrete-ring theorem d_cupHom in WeilConjectures/RepresentationTheory/GroupCohomology/CupNonvanishing.lean:165 proves cocyclicity only, with an ordinary coefficient ring; it does not state the internal derived-arrow comparison. Existing CondensedDerivedInvariantBar is infrastructure and does not state the item.

## WANTED

WANTED: a reference proving the ordinary internal condensed-module bar cocycle-roof/derived-adjunction normalization, including connecting arrows, for lem-sfb-internal-bar-roof-adjunction.

WANTED: a reference proving the derived strong monoidal trivial-inflation adjunction and its graded cup/composition normalization for internal condensed-group modules, for lem-sfb-internal-inflation-graded-cup.

The blueprint direct-images paragraph (3) gives the parent open-direct-image route, not this expanded bar argument. Both new inputs are explicitly agent formulated; no claim that the literature proves the complete internal-category statements. I read Stacks derived.tex Tag 09T5 (lemma-derived-adjoint-functors), and Tag 06XR (lemma-compute-ext-resolutions), as context. Neither is silently used as the full normalization lemma. No SGA source is used.

## Corrections and scope

The item was unsplit, with no earlier sandbox work. Its statement is retained verbatim. There is no statement dispute. The proof avoids pretending that internal free modules on profinite sets are projective, that point sections are exact, or that the underived internal-function terms are acyclic. The structural obligations concern arbitrary bar cocycles and arbitrary graded endomorphisms, not a renamed clause about ordered characters. The character chain lifts and their composition remain in the item's proof.

The ancestor command prints None for this imported chain; new nodes retain null from.node, prepend the item to the existing via list, and give a specific place in paragraph (3). Whole-blueprint searches for bar resolution, bar cocycle, derived invariant, ordered character, monoidal adjunction, graded composition, derived monoidal inflation, trivial action and monoidal invariants found no exact duplicate. The unit/chapter and GOAL were read; this lies strictly below the unit's direct-image step and does not replace its geometric route.

## Not duplicates

lem-sfb-internal-bar-roof-adjunction vs lem-sfb-condensed-derived-invariant-bar: the existing node gives a derived-object isomorphism and coefficient naturality, not the identification of a homogeneous cocycle roof and a short-exact-sequence connecting arrow under its normalized derived adjunction.

lem-sfb-internal-bar-roof-adjunction vs lem-sfb-condensed-internal-bar-resolution: the existing node gives an exact tensor-stable augmented complex and induced coordinates, not a derived adjunction or cocycle-roof normalization.

lem-sfb-internal-bar-roof-adjunction vs lem-pc-derived-adjoint-functors: the existing node gives an abstract derived adjunction; it contains no internal bar model, augmentation, cocycle comparison or connecting-cocycle computation.

lem-sfb-internal-bar-roof-adjunction vs lem-sc-p1-split-ses-cocycle-boundary: the latter concerns degreewise split short exact complexes and their boundary calculation, not an arbitrary internal nonprojective bar and its derived invariant total.

lem-sfb-internal-inflation-graded-cup vs lem-sfb-condensed-derived-restriction-calculus: the existing node supplies the cup product, normalized characters and naturality; it does not supply the strong monoidal derived inflation adjunction or identify cups with shifted composition of arbitrary equivariant endomorphisms.

lem-sfb-internal-inflation-graded-cup vs lem-sfb-monoidal-adjunction-mates: abstract transfer of monoidal structures does not establish derived tensor or strong monoidality in the internal condensed-action category or the shift-normalized composition formula.

lem-sfb-internal-inflation-graded-cup vs lem-sfb-lattice-koszul-triangulated-cup-comparison: that node treats the discrete lattice and a finite Koszul model; the new node treats profinite internal actions and canonical adjunctions with arbitrary graded endomorphisms and no Koszul assertion.

lem-sfb-internal-inflation-graded-cup vs lem-sfb-ringed-derived-monoidal-comparisons: the existing node treats specified geometric morphisms of ringed topoi, pullback composition and their tensor coherence; it does not directly state this internal action category or graded unit-endomorphism formula.

## Review by NW

I read the current blueprint direct-images proof paragraph (3), the chapter and unit records, and the actual statements of each node cited by the six steps. I read the new statements in full after writing them. Both introduce their own ring, group, module categories, universes and derived conventions; their statements contain no proof sketch and their proofs and proof dependencies are empty. They do not assume the result being proved. The underlying context tags 09T5 and 06XR were read in derived.tex, with their labels checked in tags/tags; they are context, not claimed sources for a theorem absent there.

Step 1 uses the homogeneous resolution's explicit exactness, augmentation and coordinate change, and the new inflation lemma's canonical adjunction. Step 2 uses that resolution's free internal modules and writes the character chain lift and every boundary cancellation: the sole remaining coefficient is the three-term additive-character identity. It is an elementary formula on generators, natural after every profinite base change, not a hidden acyclicity theorem. Step 3 uses the same free/coordinate statement and explicitly inducts on the number of shifted maps; it gives the product on the first q edges and proves cocyclicity by the chain-map equation. These two computational steps are elementary, and neither creates a lemma node merely for cocyclicity.

Step 4 uses the new roof lemma's boundary clause and the existing restriction calculus's actual degree-one normalization. The lift [g] -> (a(g),1) is equivariant; its boundary is (a(g1)-a(g0),0), so its sign is the prescribed positive character cocycle. Step 5 uses the new inflation lemma's shifted-composition law, with p=q and the next factor of degree one. It explicitly specifies the induction and universal sign recurrence; the cancellation of the middle augmentation inverses is categorical composition. Step 6 uses the roof lemma's actual displayed formula, not merely its existence of an adjunction, and the existing bar statement's specified augmentation. It combines the two universal signs and checks q=0,1. The citations file quotes the complete relevant statements, verbatim; there is no bending a definition into a comparison theorem.

I checked the small cases q=0 (identity roof and cup unit), q=1 (the extension-lift boundary), q=2 (a(g0^-1 g1)b(g1^-1 g2)), a zero character, the trivial group, the zero ring and characteristic two. The L_a maps have target P[1], hence the differential is -d_P; forgetting that sign would invalidate the chain-map assertion, so it is written explicitly. The bar terms need no projectivity, and the derived target comparison is never replaced by cohomology groups. All steps are shorter than 2000 characters. No new hypotheses were added to the item.

For Mathlib I read the actual hits of the recorded queries. Rep.barResolution.extIso (Resolution.lean:438) and groupCohomologyIsoExt (GroupCohomology/Basic.lean:205) concern discrete representations over an ordinary ring and the former uses projective bar terms (Resolution.lean:430). The monoidal-adjunction hits in CategoryTheory/Monoidal/Functor.lean:947 and :1036 are generic tools, not the internal derived action and shift-composition assertion. ShiftedHom.comp (ShiftedHom.lean:40) defines composition but does not identify it with cup. The second semantic phrasing for each new node returned these same insufficient discrete/general ingredients. Loogle queries with unqualified unknown names were not treated as proof of absence; the qualified/string searches and semantic/source searches supplied the useful checks. No search was invented and no unavailable service was reported as a negative match.

What remains is intentional stage-1 frontier: the two new structural statements need their own later splits. No required part of this item's split is deferred.
