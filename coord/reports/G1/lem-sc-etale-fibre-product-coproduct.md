1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-etale-fibre-product-coproduct.json`: item, split into four proof steps; no Mathlib leaf.
- `dag/nodes/sec-curve-estimates/lem-sc-etale-fibre-product-base-change-coproduct.json`: statement-only supporting node; no Mathlib leaf.
- `citations.json`: verbatim statement quotations for every proof citation.

2. Attachments: none. No sorry-free declaration with this statement was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `Comparator`.

3. WANTED: none.

4. What was checked and corrected:

The item and the new supporting node were checked against the Stacks Project Schemes source, Lemmas Tags 01JB and 01JC (labels `lemma-glue` and `lemma-glue-schemes`), together with the fibre-product universal property in Section 26.17. I searched the whole DAG and the available blueprint index for the item and for the base-change statement; the only existing related node is `lem-weil-pbc-scheme-coproduct-family`, which states the coproduct mapping property and the open, disjoint, covering coprojections. The source and node statements introduce all schemes, morphisms, finite index set, coproduct, fibre products, and projections explicitly.

Step 1 uses exactly the universal property in `def-pc-fibre-product` and the coproduct coprojections from `lem-weil-pbc-scheme-coproduct-family` to construct each indexed component map. Step 2 uses the existing node's disjoint open cover and the new base-change statement; its hypotheses are an arbitrary morphism to X and the same finite family, so the induction applies at every stage. Step 3 uses the coproduct universal property and the gluing and uniqueness supplied by Tags 01JB and 01JC to obtain the inverse and verify both composites. Step 4 is the direct projection calculation from the fibre-product universal property; it is marked elementary because it is just uniqueness after composing the defining projections. `citations.json` quotes the exact sentences used from every cited node.

I tested the statement on $p=0$ (the coproduct itself), $p=1$ (the pairwise fibre-product decomposition), a one-element index set (the canonical identity), and the empty finite index set (both sides are the empty scheme). I also checked that the omitted-factor compatibility reduces to the defining projection equations in these cases. Mathlib searches for the new base-change node used LeanSearch, LeanFinder, and source grep; none states the required scheme-level distribution isomorphism.

## Review by G1

I read the item node, the blueprint ancestor `lem-sc-etale-affine-qcoherent`, the existing coproduct node, and the new base-change node. The item statement agrees with the intended Cech decomposition: it has a finite family of maps to one scheme, the induced coproduct map, all $p+1$ iterated fibre products, and the restriction of every face projection. The new node is strictly smaller, has an arbitrary single base-change scheme, and states only the one-factor coproduct decomposition with its projection compatibility.

For each proof step I opened the cited node statements and verified the quoted content: Step 1 takes the fibre-product universal property and coprojections; Step 2 takes the open disjoint covering and the base-change decomposition; Step 3 takes the coproduct mapping property; Step 4 takes only the fibre-product uniqueness equations. No step relies on a cited node's proof or on an uncited tag as a substitute for a statement. The induction handles the empty and singleton cases, and the projection clause is checked componentwise. The only correction to the imported item was to replace its empty proof and incorrect `created.item` metadata with this split, and to add the missing smaller base-change statement required by the induction.
