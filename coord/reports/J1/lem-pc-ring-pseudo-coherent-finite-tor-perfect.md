1. Files written:

   - `dag/nodes/sec-picard-framework/lem-pc-ring-pseudo-coherent-finite-tor-perfect.json` (item, split; Mathlib searches found no exact criterion and LeanSearch was unavailable).
   - `citations.json` (verbatim statement quotes for every cited node in the item proof).

2. Attachments: none. The only project theorem with a related name, `DerivedCategory.isPerfect_of_finiteTorAmplitude`, has stronger Noetherian, boundedness, and finite-homology hypotheses and is still `sorry`; it does not state this item.

3. `WANTED: literature/stacks-project/more-algebra.tex, More on Algebra, Lemma 15.76.2 (Tag 0658), because the local literature checkout contains only the tag index, not the Stacks TeX source.`

4. What was checked and corrected: the imported item had no proof and cited a missing node `lem-pc-ring-l-finite-tor-perfect`. I searched the whole DAG, blueprint references, and both Lean source trees. The item is the ring criterion of Tag 0658, not a duplicate of the existing scheme-level direct-image criteria or the Noetherian Lean theorem. The first attempted child node was correctly rejected as moving the item's content into a new node, so I removed it and wrote the truncation argument directly as proof steps. The steps choose the bounded-above finite-projective model, form the cokernel at the lower Tor bound, derive flatness from Tor vanishing, use the existing finitely-presented-flat-projective lemma, and identify the resulting bounded finite-projective complex as perfect. I tested the edge case of a bounded complex (the truncation is immediate) and the zero complex (all terms and the replacement are zero).

## Not duplicates

lem-pc-ring-pseudo-coherent-finite-tor-perfect vs lem-weil-bounded-finite-tor-perfect: the existing node assumes a Noetherian ring and a bounded complex of finite modules, while this item assumes an arbitrary ring and pseudo-coherence via a bounded-above finite-projective resolution.

lem-pc-ring-pseudo-coherent-finite-tor-perfect vs lem-trf-finite-tor-amplitude-perfect: the existing node is only for the finite local Artinian coefficient ring and bounded finite-cohomology complexes, while this item is for every ring and arbitrary derived objects satisfying pseudo-coherence.

lem-pc-pseudo-coherent-bounded-finite-free-model vs lem-pc-ring-pseudo-coherent-finite-tor-perfect: the supporting node only constructs a finite-free resolution with an upper degree bound from pseudo-coherence and cohomology vanishing; it does not conclude boundedness, finite projectivity of the truncation, or perfectness.
lem-pc-pseudo-coherent-bounded-finite-free-model vs lem-weil-bounded-finite-tor-perfect: the existing node assumes a bounded complex of finite modules over a Noetherian ring, whereas the supporting node constructs a bounded-above finite-free model over an arbitrary ring from pseudo-coherence and an upper cohomology bound.
lem-pc-pseudo-coherent-bounded-finite-free-model vs lem-trf-finite-tor-amplitude-perfect: the existing node concerns finite local Artinian coefficients and a bounded finite-cohomology complex, whereas the supporting node is the arbitrary-ring finite-free replacement used before truncation.

## Review by J1

I read the item's Stacks source citation (More on Algebra, Tag 0658) and the surrounding blueprint clause from `lem-sc-finite-duality`; the local checkout does not contain the TeX, so the report records it as wanted. I also read `Perfect.lean` in both source checkouts: `DerivedCategory.isPerfect_of_finiteTorAmplitude` is sorry-bearing and has different hypotheses, so no attachment applies. I searched existing DAG nodes for Tag 0658, pseudo-coherence, finite Tor dimension, truncation, and projective criteria; no node states the arbitrary-ring criterion in this item.

For item steps 1, 2, and 4, the model choice, cokernel construction, and quasi-isomorphism of the brutal truncation are written directly from the Tag 0658 argument and marked elementary. Step 3 uses the existing node whose statement says that a finitely presented flat module is finite projective; its hypotheses are established in the preceding sentence. Step 5 uses the definition node's strictly-perfect clause; on an affine ring this is exactly a bounded finite-projective complex. `citations.json` quotes the exact relevant sentences.

I ran all required Mathlib searches for the item. LeanFinder returned only generic projective-dimension and K-projective declarations, Loogle returned an unknown identifier/no hits, grep returned no matching declarations, and LeanSearch was unavailable; these results are recorded verbatim with verdicts. No source statement was changed and no new node remains.

## Second reading by J1

- Item statement: checked against Stacks More on Algebra, Lemma 15.76.2 (Tag 0658), including the arbitrary-ring, pseudo-coherent, finite-Tor-amplitude hypotheses and the bounded finite-projective conclusion; verdict: direction used by the item is correct. The local checkout lacks `more-algebra.tex`; I verified the tag text from the Stacks tag page and retained the wanted-source note.
- Step 1: checked against Tag 0658's finite-free replacement and the definition nodes for derived categories and pseudo-coherence; verdict: revised to require a model vanishing above `b` and to preserve the Tor-amplitude condition.
- Step 2: checked against Tag 0658's definition of `tau_{>=a}`; verdict: revised to define the truncation and identify its finitely presented degree-`a` cokernel explicitly.
- Step 3: checked against Tag 0658's flatness argument (Lemma 15.68.2) and the cited finitely-presented-flat-projective node; verdict: revised to identify the Tor obstruction and state the resulting flatness before applying the cited node.
- Step 4: checked against the truncation conclusion in Tag 0658; verdict: revised to state why the truncation map is a quasi-isomorphism and why all terms are finite projective.
- Step 5: checked against Definition 15.76.1 (Tag 0657) and `def-pc-perfect-complex`; verdict: elementary affine identification is correct.
- Supporting node `lem-pc-pseudo-coherent-bounded-finite-free-model`: checked as a strictly smaller statement than the item, with self-contained hypotheses, Tag 15.66.5 source, blueprint metadata, and four recorded Mathlib searches; verdict: needed to cite the bounded finite-free replacement in Step 1.
- Edge cases: the zero complex gives the zero bounded projective complex; a field gives the usual bounded finite-dimensional complex; a bounded input is unchanged by the replacement; the interval endpoints allow `a=b`.

Changes: corrected the four truncation steps to match the actual Tag 0658 proof, added the supporting bounded finite-free-model node, made the upper-bound model and flatness obstruction explicit, and added this second-reading audit. No statement or dependency was weakened.
