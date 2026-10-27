# Worker report: lem-a1-strict-roos-shift-localization

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-strict-roos-shift-localization.json`: item split into six proof steps; no new nodes.
- `citations.json`: verbatim statement citations for every non-elementary dependency.

## Attachments

None: the project-source search by blueprint tag and by Roos/shift terminology found no declaration stating this item. The following existing DAG nodes are reused as dependencies, not claimed as new Lean attachments.

- `def-weil-abstract-derived-category` is the existing derived-category definition and was used for complexes, shifts, cones, and localization.
- `def-weil-strict-roos-model` is the existing strict Roos cone and limit-inclusion construction.
- `lem-weil-pbc-localization-universal-property` is the existing Mathlib leaf for lifting functors and natural transformations through a localization.

## WANTED

None.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## Review by Q24

I read the complete item statement and checked its three statement dependencies. The strict model source is `dag/nodes/sec-smooth-purity/def-weil-strict-roos-model.json`; it gives the product endomorphism, the shifted cone coordinates, diagonal map on tower morphisms, and the inclusion `(0,z)`. The derived-category source is `dag/nodes/sec-picard-framework/def-weil-abstract-derived-category.json`; it supplies the cochain shift convention and localization at quasi-isomorphisms. The localization source is `dag/nodes/sec-proper-base-change/lem-weil-pbc-localization-universal-property.json`; its statement explicitly gives existence, unique lifting of natural transformations, and equality after precomposition with the localization.

For step 1 I checked the signs against Stacks `homology.tex`, Tag 011G, and the cone convention in `derived.tex`, Tag 014E. Writing `epsilon=(-1)^r`, the shifted source differential is `(-epsilon dy-h_X x, epsilon dx)` and applying the proposed map to the target differential gives the same pair; `epsilon^2=1` proves the inverse formula. This is a biproduct-component calculation and does not assume elements in the abelian category. Step 2 uses only the diagonal product-map clause of the strict model and the same sign multiplication; it verifies naturality, the zero shift, and the additive coherence law.

Step 3 checks the termwise limit shift from the universal property of limits. The transition maps are unchanged by reindexing, and both sides of the inclusion equation have first component zero and the same second compatible tuple. Step 4 applies the existing localization statement with the quasi-isomorphisms as the inverted class; the two functors are exactly `G(-[r])` and `G(-)[r]`, and the component is the conjugate of the strict comparison by `kappa`. The hypotheses that both functors invert the class follow because they factor through `Q_T`. Step 5 checks the zero and successive-shift laws after substitution and cancellation of adjacent `kappa` factors, then uses the same localization uniqueness clause to extend equality from localized objects to every derived object. The argument also explicitly covers inverse morphisms of quasi-isomorphisms. Step 6 substitutes the inclusion identity into the defining comparison equation and obtains the required commutation with the localized termwise limit inclusion.

I supplied the formerly empty proof by writing the sign calculation, the limit-inclusion calculation, and the localization naturality hypotheses as separate steps. The existing strict Roos and localization nodes already state the required ingredients, so creating a new dependency node would have duplicated existing facts.

I tested the coordinate identities for the zero complex, for $r=0$, for $r=1$ and $r=-1$, and for two successive odd shifts (their product has positive sign). In characteristic two the negative and positive signs coincide and all formulas still agree. A constant tower concentrated in one degree has $h j=0$ and the same zero first coordinate, so the inclusion calculation has no hidden surjectivity or exact-products hypothesis. Unboundedness causes no infinite summation: the only matrix computation is a binary biproduct, with countable products used degreewise. Ordinary termwise limit is never descended as a functor on the derived category.

The DAG and whole-blueprint searches included Roos, shift localization, localization universal, and endomorphism fibre. The existing universal-property leaf suffices for descent and equality; the endomorphism-fibre node was inspected but not needed, since the signed-coordinate calculation is short enough to write in the item itself. All Mathlib searches in this session used the prescribed msearch command and are retained in searches.jsonl, with two semantic phrasings. I read the cone-shift hits and the localization implementations in Mathlib/CategoryTheory/Shift/Localization.lean and Mathlib/CategoryTheory/Localization/Predicate.lean. They supply general machinery, not an exact project declaration stating this item. No statement or hypothesis was changed; there is no source dispute, no new lemma, no long proof step hiding a comparison lemma, and no remaining unfinished part of this stage-1 split.
