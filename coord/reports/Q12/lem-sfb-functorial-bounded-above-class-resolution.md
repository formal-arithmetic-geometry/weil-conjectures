# Stage 1 report

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-functorial-bounded-above-class-resolution.json`: split item, no statement change.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-reduced-class.json`: new unsplit statement node; Mathlib searches found only the generic idempotent-completion and reduced-left-resolution machinery, so it is not a Mathlib leaf.
- `dag/nodes/sec-proetale-coefficients/lem-sfb-left-resolution-bounded-minus.json`: new unsplit statement node; Mathlib searches found objectwise `LeftResolution` APIs but not the bounded-above totalization, so it is not a Mathlib leaf.
- `citations.json`: verbatim citations for both item proof steps.

## Attachments

None. No single declaration in `WeilConjectures/` states the item exactly.

## WANTED

None. The blueprint route and the project source needed for the split are present locally.

## Not duplicates

- `lem-sfb-left-resolution-reduced-class` vs `lem-sfb-subcategory-left-resolution`: the existing node gives an objectwise bounded-above resolution for one chosen upper bound; the new node constructs a zero-preserving functorial cover datum from the class and direct-summand hypothesis.
- `lem-sfb-left-resolution-bounded-minus` vs `lem-sfb-subcategory-left-resolution`: the existing node is existential and fixed-bound; the new node gives one functor and natural augmentation on the full bounded-above category, including maps with different bounds.
- `lem-sfb-left-resolution-bounded-minus` vs `lem-sfb-unbounded-kflat-resolution-existence`: the existing node concerns unbounded K-flat replacements and does not preserve bounded support or provide a bounded-minus functor; the new node concerns bounded-above totalization before K-flat arguments.

## Review by Q12

I read the item, the `sec-proetale-coefficients` chapter and `sk-def-sfb-derived-tensor-hom` unit, and the parent proof `lem-sfb-derived-monoidal.proof.md`. I also read the source implementation in `FromJoel/Algebra/Homology/LeftResolution/CochainComplexMinus.lean` (lines 32–275), `FromJoel/Algebra/Homology/LeftResolution/CochainComplex.lean` (lines 35–103), and Mathlib `Algebra/Homology/LeftResolution/Basic.lean` and `Reduced.lean` (especially the `karoubi`/`reduced` definitions and the retract proof of epimorphy). These sources establish that a functorial object cover can be reduced to one preserving zero morphisms and that the bicomplex totalization is defined for every bounded-above complex, is functorial in all maps, is quasi-isomorphic to the input, and retains any supplied upper bound.

For item step 1, I checked that [lem-sfb-left-resolution-reduced-class] states exactly the datum used: preadditive category with zero and finite coproducts, fully faithful additive inclusion, zero-preserving cover functor, epimorphic natural transformation, and values in the original class. The abelian-category and direct-summand hypotheses are the ones needed for finite biproducts and idempotent completion; no additivity of the original `P` was silently assumed. For step 2, I checked that [lem-sfb-left-resolution-bounded-minus] supplies one functor on the full bounded-above subcategory, a natural quasi-isomorphic augmentation, terms in the essential image, and preservation of every upper bound. The isomorphism closure of `\\mathcal F` then gives the item's term condition. I tested the edge cases conceptually: the zero complex is sent to a bounded-above zero-preserving resolution, and a complex concentrated in one degree keeps that degree as an upper bound. The two new nodes were searched in the DAG and blueprint before creation; their four recorded Mathlib searches are the actual `msearch.py` results, with invalid Loogle identifiers recorded as such rather than treated as matches.
