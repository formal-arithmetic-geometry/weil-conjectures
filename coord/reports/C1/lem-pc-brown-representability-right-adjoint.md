1. Files written:

   - `lem-pc-brown-representability-right-adjoint.json`: item split into four proof steps; 0 Mathlib leaves.
   - `lem-pc-brown-cohomological-representability.json`: statement-only dependency; Mathlib no-match.
   - `citations.json`: verbatim citations for steps 3 and 4.

2. Attachments: none.

3. WANTED: none.

4. The original item had no proof or proof dependencies. I checked the Brown criterion against Stacks Project Tag 0F5Y (Proposition 19.15.2) and the use of the same criterion in the existing derived direct-image node. The new dependency is strictly smaller: it states representability of one contravariant cohomological functor, rather than existence of a right adjoint for a functor between triangulated categories. I searched all DAG nodes and blueprint text for Brown representability and cohomological representability before creating it. Mathlib searches found only general homological-functor and Yoneda declarations, not Brown representability.

## Not duplicates

lem-pc-brown-cohomological-representability vs thm-amb-etale-exceptional-adjoint: the new node states the generic representability theorem for every cohomological functor on a compactly generated triangulated category, while the existing node states only the application giving a right adjoint to the ordinary etale compact-support functor for a compactifiable morphism of Noetherian schemes.

## Review by C1

I read the item source reference (Stacks `injectives.tex`, Proposition `injectives-proposition-brown`, Tag `0F5Y`) and checked its hypotheses against the item: C is triangulated and compactly generated with set-indexed coproducts, F is exact and coproduct-preserving, and D is triangulated with the stated coproducts. Step 1 uses only the definition of exactness and the standard long exact Hom sequence, so it is marked elementary. Step 2 uses only preservation of coproducts and the Hom-out-of-coproduct isomorphism, also elementary. Step 3 cites the new node, whose statement exactly supplies representability for the cohomological functor constructed in steps 1–2. Step 4 uses the same statement and spells out the Yoneda uniqueness argument that makes the representing objects functorial and yields the adjunction. I verified every citation quote is copied verbatim from the new node statement, and tested the construction on the zero functor and on an identity functor: the representing object is respectively a zero object and the input object, as expected. No Lean declaration states the item, and Mathlib has no Brown representability theorem.

5. The Stacks TeX checkout was available at `/home/ubuntu/c1-stacks-review`; the source was rechecked there during second reading.

## Second reading by C1

- Item statement: checked against `/home/ubuntu/c1-stacks-review/derived.tex`, Proposition `proposition-brown`, Tag `0A8G`; verdict: hypotheses and right-adjoint conclusion match.
- Step 1: checked against the proof of Proposition `proposition-brown` and Lemma `lemma-brown`, Tag `0A8F`; verdict: the Hom construction is the stated cohomological functor.
- Step 2: checked against the direct-sum preservation clause of Proposition `proposition-brown`; verdict: preservation gives the required product map.
- Step 3: checked against Lemma `lemma-brown`, Tag `0A8F`; verdict: the cited representability statement supplies exactly the representing object and natural isomorphisms.
- Step 4: checked against the final adjunction argument in Proposition `proposition-brown`, Tag `0A8G`; verdict: the Yoneda construction gives a functor and the adjunction.
- `lem-pc-brown-cohomological-representability`: checked against Lemma `lemma-brown`, Tag `0A8F`; verdict: statement matches after spelling out the category and coproduct/product condition.

Changes: corrected the item and dependency source references from the unrelated `injectives.tex` Tag `0F5Y` to `derived.tex` Tags `0A8G` and `0A8F`, and recorded the source-checked verdicts above.
