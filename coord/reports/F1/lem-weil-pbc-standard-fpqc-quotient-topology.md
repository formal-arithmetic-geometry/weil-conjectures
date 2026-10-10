# Stage 1 report

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-standard-fpqc-quotient-topology.json`: item split, with four proof steps.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-flat-qc-surjective-quotient-map.json`: new statement node, Mathlib exact match `AlgebraicGeometry.Flat.isQuotientMap_of_surjective`.
- `citations.json`: verbatim statement quotes for every step citation.

## Attachments

None. No sorry-free declaration in either Lean checkout carries the item tag or its statement.

## WANTED

None. The source statement and proof are Tag 02JY in the Stacks Project; the pinned Mathlib declaration supplies the quotient-map fact.

## Not duplicates

- `lem-weil-pbc-flat-qc-surjective-quotient-map` vs `lem-weil-pbc-standard-fpqc-quotient-topology`: the new node is the one-morphism theorem for arbitrary schemes with flat, quasi-compact, and surjective hypotheses; the item is its finite affine-family specialization via a product spectrum.
- `lem-weil-pbc-flat-qc-surjective-quotient-map` vs `lem-weil-pbc-fpqc-descend-universally-closed`: the existing node merely cites Tag 02JY as an ingredient in descent of universal closedness and does not state a quotient-map theorem; the new node states the general quotient-map open-set equivalence.

## What was checked

I read the imported item and its parent `lem-weil-pbc-open-subscheme-fpqc-descent`, and checked the route against Morphisms Lemma Tag 02JY and the affine/refinement paragraph of Descent Lemma Tag 03N0. The item statement has the same affine base, finite affine family, faithful-flat product map, and openness hypothesis as the intended specialization. No completed declaration with this item id, tag, or conclusion exists in `WeilConjectures` of either checkout.

Step 1 uses the existing affine-morphism permanence statement for the fact that a finite coproduct of affine schemes is affine, and the existing scheme-coproduct statement for open disjoint summands covering the coproduct; both statements explicitly say the facts used. Step 2 uses the faithful-flat definition's flatness clause, the affine-spectrum flatness equivalence, affine morphism quasi-compactness, and the faithful-flat spectrum-surjectivity node; I opened each node and verified its quoted sentence. Step 3 uses the new Mathlib leaf, whose statement is exactly the quotient-map open-set criterion and whose source lines 124-126 were read. Step 4 is elementary from the coproduct open cover: a subset of a space covered by open summands is open iff each summand intersection is open, and those intersections are the given inverse images.

The new node was searched before creation with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such. The item itself was searched with the required tools earlier in this work. I tested the construction on a one-member family (the ordinary affine faithfully-flat quotient criterion), the identity family, and the empty/zero-ring edge case; no hypothesis is silently added. The new node is strictly more general than the item and does not restate its finite-family clause.

## Review by F1

I checked every proof step against the cited node statements and the Tag 02JY source. Step 1's affine coproduct and open-summand claims are exactly the two cited statements. Step 2's flatness, quasi-compactness, and surjectivity claims are respectively supplied by the four cited statements; the induced map is the spectrum map of the product ring, so the hypotheses apply. Step 3 takes precisely the open-set equivalence from the new Mathlib declaration. Step 4 only unfolds the open coproduct cover and identifies each restriction with $f_j^{-1}(W)$, so it is elementary. I also checked the affine, one-member, and empty-family edge cases and verified that the new node's Mathlib line and search records agree with the pinned source.

## Second reading by F1

- Item statement: checked against Morphisms Lemma Tag 02JY (`morphisms.tex`, label `lemma-fpqc-quotient-topology`) and the finite coproduct specialization; verdict: the finite-family open-subset implication has exactly the stated hypotheses and conclusion.
- Step 1: checked against Tag 03N0's affine standard-cover paragraph and all cited statements; verdict: the previously implicit finite coproduct/product-spectrum identification is now explicitly cited.
- Step 2: checked against Tag 02JY's affine proof, the faithful-flat definition, affine flatness equivalence, affine quasi-compactness, and spectrum surjectivity; verdict: all hypotheses for the Mathlib quotient-map leaf are present.
- Step 3: checked against Mathlib `AlgebraicGeometry.Flat.isQuotientMap_of_surjective` and Tag 02JY; verdict: exact open-set quotient criterion.
- Step 4: checked against the open coprojection cover statement and the topology of an open cover; verdict: elementary two-inclusion argument, with the component intersections identified as $f_j^{-1}(W)$.
- `lem-weil-pbc-flat-qc-surjective-quotient-map`: checked against Mathlib `Flat.lean` lines 124-126 and its recorded searches; verdict: exact Mathlib leaf.
- `lem-weil-pbc-finite-affine-coproduct-spectrum`: checked against Mathlib `Limits.lean` lines 604-613 and 641-647 and recorded LeanFinder/Loogle/grep searches; verdict: exact finite-index `sigmaSpec` isomorphism and coprojection formula.
- Small cases checked: one-member family, identity map, empty family (forcing the empty affine base under faithful flatness), and zero product ring.
- Changes: corrected all Tag 02JY source paths from `more-morphisms.tex` to `morphisms.tex`; added the finite affine coproduct/product-spectrum Mathlib leaf and its citation; updated Step 1, proof dependencies, citations, and search records to close the identification gap.
