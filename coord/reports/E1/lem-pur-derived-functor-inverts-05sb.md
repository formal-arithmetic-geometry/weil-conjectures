1. Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-derived-functor-inverts-05sb.json` — statement, split proof, no new nodes, Mathlib searches recorded in the item.
- `citations.json` — verbatim citations for both proof steps.

2. Attachments: none.

3. WANTED: none.

4. The imported item had no proof. The Stacks source (`/home/ubuntu/c1-stacks-review/derived.tex`, Lemma `lemma-derived-inverts`, corresponding to Tag 05SB) explicitly says the proof is omitted. I therefore supplied the omitted calculus-of-fractions argument from Situation 05S8: MS2 and MS3 compare the denominator categories, and Lemma 05SA(2) gives the induced map and its uniqueness. The statement and hypotheses were kept unchanged.

## Review by E1

I read the item's source, the parent definition node, and the 05SA morphism node. Step 1 uses the exact MS2 and MS3 clauses in `def-pur-saturated-triangulated-localization` to transport essential constancy between `S/X` and `S/Y`; the hypotheses that `s` lies in `S` and that the denominator categories are the Definition 05S9 pro-diagrams are present in the item and parent definition. Step 2 uses the exact uniqueness-and-commutative-square assertion of `lem-pur-derived-functor-morphisms-05sa`, with the same MS2/MS3 clauses to choose a reverse map and identify both composites after common refinement. I checked the Mathlib search log: LeanFinder found only the general pointwise-derived APIs, Loogle was unavailable, grep found the general inversion declarations, and LeanSearch was unavailable; none states the Stacks pro-object lemma exactly. No duplicate or new auxiliary node was needed.

5. Nothing remains unfinished.

## Second reading by E1

- Item statement: checked against `derived.tex`, Lemma `lemma-derived-inverts`, part (2) (Tag 05SB), and Situation 05S8; verdict: the LF-defined-at-X/Y equivalence and the isomorphism conclusion agree hypothesis by hypothesis.
- Step 1: checked every use of MS2 and MS3 against `def-pur-saturated-triangulated-localization`; verdict: the two denominator comparisons, refinement independence, and preservation of essential constancy are stated explicitly.
- Step 2: checked the induced map and uniqueness against `lem-pur-derived-functor-morphisms-05sa`, and the reverse squares and refinements against MS2/MS3; verdict: the inverse construction and both identity composites are now explicit.
- New nodes: none; B1-B7 and duplicate search are vacuous for this split. The two cited nodes were read in full and provide the only non-elementary inputs.
- Edge cases: identity denominators and the zero/identity morphism give the identity LF map; the argument uses no nonzero or field hypothesis, so it also covers the zero triangulated category and a field-based example.
- Changes made: clarified both proof steps to spell out the MS2 square orientations, MS3 refinement arguments, and the use of 05SA uniqueness; retained the imported item's maintainer-owned `created` metadata unchanged.
