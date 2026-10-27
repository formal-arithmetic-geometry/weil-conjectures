# Q35: lem-sfb-affine-koszul-low-localization

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-affine-koszul-low-localization.json`: statement, corrected endpoint and seven-step split, not a Mathlib leaf.
- `citations.json`: 21 step/citation entries, quoting the actual statements read.
- `searches.jsonl`: actual msearch output records; the item's inherited searches are preserved and the present searches appended.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0. The sandbox began without an item or previous split. Only the sandbox was written. No compiler, Lake, build or repository git command was run.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint id and for Koszul orthogonality, bounds and localization found no declaration giving this quantitative assertion. I read `AlgebraicGeometry.koszul_open_orthogonality` in `AlgebraicGeometry/KoszulOpenOrthogonality.lean` and `AlgebraicGeometry.koszul_powers_orthogonal_of_orthogonal` in `AlgebraicGeometry/KoszulPowersOrthogonality.lean`. They assume vanishing in ALL shifts. They do not discharge the bounded-range hypothesis of this item, so I did not attach them or apply the all-shifts powers theorem.

## WANTED

None. The required Stacks TeX is available locally.

## Source error

STATEMENT-DISPUTED: the imported statement and Stacks Tag 0GEK, `perfect-lemma-orthogonal-koszul-second-variant`, have a false endpoint. This is an error in the source itself, not merely an insufficient imported proof. I also checked the public page https://stacks.math.columbia.edu/tag/0GEK; it has the same endpoint and cone-shift error as the local TeX.

Take A = Z, r = 1, f_1 = 2, E = O_Spec(Z)[0], and a = 0. The actual cochain Koszul complex is [Z --2--> Z] in degrees -1, 0. Its derived Hom into Z is computed by [Z --(plus or minus 2)--> Z] in degrees 0, 1, because the Koszul terms are finite free. Its H^0 is zero and all its negative cohomology is zero. Under the affine derived equivalence, therefore Hom(C_f[-n],E) is zero for every n <= 0, exactly the item's hypothesis. But the unit has degree-zero global sections Z -> Z[1/2], which is not surjective. Hence its truncation at <= 0 cannot be an isomorphism.

For the source's cone triangle E -> B -> N -> E[1], with B = Rj_*j^*E, Hom(C_f[-n],B) vanishes in every degree, so the correct identification is Hom(C_f[-n],N) = Hom(C_f[-(n+1)],E), not the same n. The source incorrectly drops this shift. Thus the cone is shown to have zero cohomology in degrees <= a-1, and the unit is an isomorphism after truncation at <= a-1. I corrected both displayed truncations in the statement from a to a-1, preserving all hypotheses, objects and the canonical morphism. An equivalent formulation would keep truncation at a and require Hom vanishing through a+1.

The unit and chapter routes are unchanged. In particular the application is to eventual low-degree vanishing, for which subtracting one from an arbitrary integer bound has no effect on the conclusion of the parent lemma. The proof follows the source's Koszul multiplication and supported-cohomology route; the numerical error is repaired explicitly rather than bypassed.

## Statement corrected

The single direct citer is `lem-sfb-space-supported-koszul-low-localization`, Step 4. Its statement only requires existence of an integer truncation bound, and remains true. Its present Step 4 needs this explicit repair: choose a such that Hom(B,E_V[n]) = 0 for every n <= a+1, possible by the same eventual vanishing; apply the corrected affine item with parameter a+1 to obtain the required comparison at <= a. Equivalently, rename its current bound b and use a=b-1 thereafter. Steps 5 and all downstream statements are then unchanged. I have not edited that other worker's node. This proof adjustment should be recorded by the maintainer when the correction lands.

## Not duplicates

No new node was created. The existing `lem-sfb-affine-koszul-upper-localization` is the upper-truncation assertion (0GEJ), not this lower-truncation assertion. It supplied the inventory of reusable generic inputs, all of which I opened and read. The 09IR nodes impose all-shift orthogonality, not the present half-line hypothesis. `lem-pc-koszul-powers-orthogonality` likewise cannot be applied to the present assumption; the bounded-range induction is actually written in Step 3. Whole-DAG searches for 0GEK, 0GEJ, 09IR, orthogonality, powers and closed-class representation, together with blueprint_refs searches for Koszul, orthogonal and 0GEK, found no duplicate of the corrected item. The current blueprint's direct-images node and unit were read under `literature/blueprint/latest/` only. The pre-existing ancestor chain ends at null (`blueprint_refs.py ancestor` prints None); the inherited precise place and via chain are retained, and `same_as` is empty.

## Review by Q35

I read the item against `literature/stacks-project/perfect.tex`, the entire statement and proof of `lemma-orthogonal-koszul-second-variant` (0GEK), its predecessor 0GEJ, the closed-class representation paragraph and proof, the open cohomology comparison (08DD), and `lemma-affine-compare-bounded` (06Z0). For the multiplication step I read `literature/stacks-project/more-algebra.tex`, `lemma-koszul-mult` and its abstract predecessor (062C), and the Koszul homotopy lemma (0663). There are no new nodes needing independent sources. I read the current blueprint's ctf-stability unit, the direct-images statement and its proof (3), as well as the stored chapter/unit records and the parent's Steps 4--5. This is a Zariski structure-sheaf tool below that route, not a replacement by an etale or pro-etale coefficient category. No SGA source is used.

For Step 1 I checked the statements of `lem-weil-pbc-spec-localization-away-basic-open` and `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`: they give the basic-open homeomorphism and compactness of every spectrum. Taking a finite union proves compactness of W without a separate lemma. `lem-pc-ringed-spaces-derived-adjoint-general` supplies exactly the required unbounded adjunction; for an open immersion its left side is restriction, by its tensor formula. `def-weil-triangulated-category` permits the unit cone and rotations. `lem-pc-derived-open-unit-cone` is stated for any right adjoint to exact open restriction and the specified adjunction unit, so it applies to this B; its compact-open and quasi-coherence hypotheses are verified. Its conclusion gives BOTH quasi-coherence of N and zero restriction, which later steps need.

For Step 2 I read `lem-pc-koszul-restriction-zero` and checked that its Koszul convention agrees exactly with the item's placement in negative cochain degrees. It applies also to every shift and the empty tuple. The adjunction node gives zero Hom into B; no informal assertion about the Hom of a cone is used. `lem-weil-pbc-hom-into-triangle-exact` (ii), applied to B -> N -> E[1], factors each map through B after its composite into E[1] is zero. I wrote out the shift n+1 and checked the inequality n <= a-1 implies n+1 <= a. This corrects the false endpoint in the source.

For Step 3 I read `lem-pc-koszul-coordinate-mul-triangle`: its statement gives the precise middle product and two outer single-factor Koszul objects in the derived category, with no regular-sequence hypothesis. The induction measure is sum(e_i-1), the base is Step 2, and both outer tuples have smaller measure. `lem-weil-pbc-hom-out-of-triangle-exact` (i) then kills the middle Hom at that SAME n. This proof really preserves the range n <= a-1; it does not appeal to the all-shifts theorem or silently shift the range during induction.

For Step 4 I read `lem-pc-koszul-supported-augmentation-vanishing`: it gives exactly the vanishing of the tail-augmentation composite for each map O[-n] -> N. Its only hypotheses are quasi-coherence and zero open restriction, supplied in Step 1. Its natural-number index e means exponent e+1, which is explicitly reconciled with the positive-exponent convention in `lem-sc-affine-perfect-open-represent-cohomology`. The latter statement includes the actual triangle I -> O -> K -> I[1]. Hom-out exactness (i) factors the map through K[-n], and Step 3 kills that factor. No conclusion is extracted just from a definition of the tail system.

For Step 5 I checked `lem-pc-derived-structure-sheaf-hom-hypercohomology`, which states the natural additive bijection for every unbounded derived object. Apply it to N[n]. The triangulated equivalence in `lem-pc-affine-qcoh-derived-equivalence` explicitly has quasi-inverse RΓ and sends shifted free rank-one modules to shifted structure sheaves; N has its required quasi-coherence. I also read `new-affine-derived-tilde-homology-comparison`: it provides the degreewise comparison for the termwise associated-sheaf functor, exactly the functor used in that equivalence. Thus H^n(N) is the associated sheaf of H^n(RΓN), which is zero for n <= a-1. Mere conservativity of an unspecified equivalence would not prove this cohomological assertion.

For Step 6 I read all clauses of `lem-weil-heart-short-exact-triangles`, using specifically its unbounded cohomological-functor clause (5). The cone triangle has outside terms H^(n-1)(N) and H^n(N), both zero for n <= a-1; the endpoint does not require H^a(N). The standard truncation node specifies the cohomological truncation and the t-structure. For Step 7 the derived-category definition, the quasi-isomorphism calculus node and the right-fraction-representation node give a roof with quasi-isomorphic denominator. If the roof is an isomorphism on cohomology the numerator is also quasi-isomorphic, so both arrows are inverted. That last argument is elementary from those cited statements and is marked as such. All citation evidence is copied verbatim in citations.json, including the elementary step's citations.

I tested the repaired assertion on r=0 (W empty, Hom(O[-n],E)=H^n(RΓE), so it even gives the stronger zero truncation through a), f=0 (W empty and the Koszul complex splits into shifts, consistent with the result), a unit among the f_i (W=Y and the unit is an isomorphism), the zero ring (all objects zero), and the explicit Z,2 example that falsifies the old endpoint. Shifting that example by arbitrary integers shows this is a real endpoint error for arbitrary a. No reducedness, regularity, noetherianity, boundedness or nonzero-ring hypothesis has been inserted.

I checked delivery-errors B through E individually: every object and non-elementary input is already defined by the item or a cited statement; no new statement-only node, duplicate or disguised clause was manufactured; all new search entries are the queries actually logged by msearch; the seven steps carry the actual argument; there is no appeal to the proof of a cited node; and the range and exponent conventions are explicit. The new semantic searches return generic Ext, derived-support, t-structure and fraction facts, while Loogle and the relevant grep have no Koszul/localization match. I tried a second semantic phrasing of the corrected statement before deciding there is no Mathlib leaf. All non-elementary steps are shorter than 2000 characters (longest 955), and none hides an additional unproved comparison. The generic inputs from other units are all declared as tool uses in split_report; their Zariski/triangulated statements are not used to replace a unit's geometric proof step.

## Unfinished work

None in this split. The parent proof-bound adjustment and the Stacks source error are explicitly reported above for maintainer follow-up; the corrected item has a complete proof using existing DAG nodes.
