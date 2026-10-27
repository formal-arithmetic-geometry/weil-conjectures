## Files written

- dag/nodes/sec-trace-formula/lem-trf-point-cone-lifts-chain-naturality.json: item, statement; split into eight elementary coordinate calculations. Not a Mathlib leaf.
- citations.json: eight entries quoting verbatim the four existing definition statements used by the proof.
- searches.jsonl: actual searches run through the mandated msearch.py command. No new nodes; zero Mathlib leaves.

## Attachments

None. Searched WeilConjectures/ for the exact blueprint tag and for point-cone, Roos, sectionsRoos, reduction naturality and tensor insertion. ReductionDatum.complexMap_naturality only covers abstract reduction naturality; it does not cover the whole item. Related sectionsRoos declarations are under Sheaf/, and the nearby point-transport source includes sorry declarations; neither supplies a completed project declaration under WeilConjectures/ stating all clauses.

## WANTED

None. The blueprint, Stacks sites-modules.tex and derived.tex are present and were read.

## Corrections and scope

The item statement is unchanged. Its proof was empty. This delivery expands the strict representative-level calculation required by blueprint main-20261015, prop-trf-rational-frobenius-integral-model, proof clause (3), as specified by the inherited point-transport supplement. It does not change the chapter or unit route. The unit sk-d-weil is a definition unit with no proof steps to realize, and this item is not its key statement.

No auxiliary lemma was necessary: the tensor-unit, transition, signed cone and product-projection equalities are written out, rather than moved into new nodes. Definitions from other units are used as definitions, not as an alternative proof route. No off-unit theorem is used as a tool. No SGA source is used.

## Not duplicates

No new nodes. The whole-DAG keyword searches and blueprint searches for Roos, inverse-image, chain natural and cone lifts found related constructions, but no imported blueprint node stating this same collection of strict equalities. Retained blueprint.same_as = [].

## Review by Q11

I read the item's statement, its blueprint ancestor proof clause (3), the trace-formula chapter record, the sk-d-weil unit record, and the statements of every definition cited in the eight proof steps. For the mathematical construction I read Stacks Tag 03EK (sites-modules-section-tensor-product), Tag 03D6 (sites-modules-definition-pushforward, including its pullback clause (2)), and Tag 08TC (derived-definition-derived-limit). The last supplies context for the Roos construction; the proof uses the fixed strict signed cone of the item, not uniqueness of an unspecified derived-limit object. No new node needs a separate source review.

Step 1 uses def-pur-sheaf-tensor-product's sectionwise presheaf tensor formula and def-weil-pbc-sheafification's unique factorization. Those statements give precisely the construction being calculated: coefficient reduction sends 1 to 1, and the degreewise differential acts on the first tensor factor. The displayed equalities commute with restrictions, so the unique extensions to sheaves agree.

Step 2 uses def-weil-inverse-image-pullback-comparison (a) and (b). I checked that (a) actually specifies a chain representative x mapped to x tensor 1, while (b) specifies the actual coefficient-induced transition, the integral action, and the equation relating c_O to its finite projections. The proof explicitly applies reduction to the second factor and g^{-1}(t_n) to the first; it does not silently replace the transition by a derived normalization isomorphism. The scheme automorphism and the integral coefficient sheaf are exactly those of the item. Step 3 uses the same definition's explicit signed cone-lift formula; it substitutes strict compatibility to make the first coordinate zero, and checks the second differential directly.

Step 4 has no external theorem: strict tower compatibility is f_n w_X,n = w_Y,n f_(n+1), checked in each degree, and the proof expands (1-s) and the signed differential. I corrected a notation typo in this compatibility before delivery, replacing a product map where the level map f_n was required. The calculation keeps the degree i-1 map on the shifted coordinate and degree i map on the unshifted coordinate. Composition and identity are calculated by the same diagonal formula.

Step 5 uses def-trf-point-sections-roos-comparison's two projection normalizations and the explicitly stated joint determination by these projections. On the shifted coordinate both composites are Gamma(f_n^(i-1)) applied to b_n, and on the unshifted coordinate they are Gamma(f_n^i) applied to a_n. Evaluation respects composition directly. Existence or exactness of products is not reproved or assumed from an unrelated statement: c_X is precisely the comparison supplied in the item and its cited definition.

Step 6 again uses the tensor/sheafification definitions and comparison (a),(b). Both sides of each claimed naturality map are evaluated on x tensor a or y tensor 1, and the compatible coefficient reductions give strict tower maps. I made the reduction-transition subscripts explicit as t_(P,n) and t_(P',n), avoiding confusion with v_n. Step 7 substitutes these identities into both cone coordinates, including the shifted zero. Step 8 only composes strict equalities already proved, using the hypothesis on u(P); it also verifies the shifted component remains zero. These last three steps use no unstated descent or resolution theorem.

I checked small cases: P=0; h=0 and h=identity; complexes concentrated in one degree; towers with identity transitions (so 1-s is the ordinary difference operator); and the zero strict tower map. The signed differential sends (0,jz) to (0,jdz) precisely because j_n=w_n j_(n+1), and the n=1 boundary only uses the existing transition from level 2. No flatness, completeness, or quasi-isomorphism hypothesis is used beyond those given; the calculation even works for arbitrary complexes with the displayed constructions. Integral R-linearity on inverse image is taken from the exact action formula in comparison (b), not from treating the completed coefficient sheaf as constant.

Against delivery-errors B-E: there are no new objects or unsupported leaf claims, no copied clause as a new lemma, no hidden induction, and no assertion of canonical derived-limit uniqueness. Each cited statement was opened and its quotation verified literally; no proof of a cited node is used. Every non-elementary prerequisite is already part of those definitions or the item's fixed data. All eight steps are under 2000 characters. The Mathlib searches used both semantic phrasings and Loogle plus grep; the general mappingCocone.lift constructor was read at Mathlib/Algebra/Homology/HomotopyCategory/MappingCocone.lean:282 with its projections at lines 296 and 301. It does not assert the quotient/inverse-image/section normalization conjunction of this item. Existing search history was preserved; the new records are copied from the actual query log, and no unavailable result was called a negative match.

## Unfinished work

None in the split. Server dry run and direct delivery follow this report.
