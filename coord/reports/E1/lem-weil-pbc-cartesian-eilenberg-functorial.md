# Delivery report

Files written:

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-cartesian-eilenberg-functorial.json` — repaired item bounds, induction, dependencies, and split report.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-horseshoe-morphism-lift-exact-source.json` — new statement-only exact-source horseshoe lift; Mathlib verdict no match.
- `citations.json` — verbatim citations for every step.

Attachments: none.

WANTED: none.

The returned comparison node was removed because it was false without a monomorphic augmentation and duplicated the existing injective quasi-isomorphism lift. The replacement node states the needed horseshoe middle lift when the source is only a short exact sequence of exact augmented complexes. The item restores the exchanged-index bounds and realizes the decomposition, induction, vertical factorization, and totalization route.

## Not duplicates

`lem-weil-pbc-horseshoe-morphism-lift-exact-source` vs `lem-weil-pbc-horseshoe-morphism-lift`: the existing node requires injective source resolutions in all three rows, whereas the new node permits exact augmented source complexes and uses only the target horseshoe resolution.

`lem-weil-pbc-horseshoe-morphism-lift-exact-source` vs `lem-weil-pbc-lift-along-injective-quasi-iso`: the existing node lifts across a monomorphic quasi-isomorphism into a bounded-below injective complex, whereas the new node supplies compatible middle maps for a short exact sequence and a target horseshoe.

`lem-weil-pbc-horseshoe-morphism-lift-exact-source` vs `lem-weil-pbc-injective-resolution-lift-exists`: the existing node lifts one map between injective resolutions, whereas the new node lifts the middle map in a short exact horseshoe diagram with exact source rows.

`lem-weil-pbc-horseshoe-morphism-lift-exact-source` vs `lem-weil-pbc-cartesian-eilenberg-functorial`: the item asserts the full functorial Cartan--Eilenberg double-complex and totalization theorem, whereas the new node is only the exact-source middle-lift ingredient.

`lem-weil-pbc-horseshoe-morphism-lift-exact-source` vs `lem-sp-cartan-eilenberg-properties`: the existing node records the six Cartan--Eilenberg resolution properties, whereas the new node concerns a morphism of short exact rows into a target horseshoe and has no Eilenberg functoriality conclusion.

`lem-weil-pbc-horseshoe-morphism-lift-exact-source` vs `lem-sp-cart-eilenberg-left-exact-cohomology`: the existing node compares left-exact functor cohomology with cohomology of a Cartan--Eilenberg column, whereas the new node constructs compatible middle maps for exact augmented short exact complexes.

## Review by E1

I read the item source in `literature/stacks-project/derived.tex` at Definition 015H, Lemma 015I, and Remark 015K, and checked the exchanged-index bounds against `lem-sp-cartan-eilenberg-properties`. I read `lem-weil-pbc-lift-along-injective-quasi-iso` and verified that it is used only for the Z and H rows, where the exact augmented source gives a monomorphic quasi-isomorphism. I read `lem-weil-pbc-horseshoe-morphism-lift` and made the new exact-source node state the additional middle-map fact needed for the K and Z rows; its source rows are explicitly only exact augmented complexes.

Step 1 uses the six Cartan--Eilenberg conditions and exactness of `F`. Step 2 uses the quasi-isomorphism lift for Z and H and the exact-source horseshoe lift for the middle rows; the K-row maps are the horseshoe `phi_B` maps themselves, so no independent re-choice is made. Step 3 uses the boundary/cycle factorization and those three-term compatibilities. Step 4 uses the total-complex and filtration definitions; bidegree preservation and the restored bounds give finite sums. I removed the false comparison node and checked the identity case `F = id`, `K = L`, and `u = id` with identical resolutions. Mathlib searches were rerun for the item and new node; LeanSearch was unavailable and recorded as such.

## Second reading by E1

- Item statement: checked against Stacks `015H`, `015I`, and `015K`; restored `(1) I^{p,q}=0 for q<i` and `(2) I^{p,q}=0 for p<0`.
- Step 1: checked the cycle/boundary short exact sequences against `015I`; exactness of `F` is the operation used.
- Step 2: checked the induction lifts against the quoted quasi-isomorphism and exact-source horseshoe statements; verified that the K maps are the horseshoe middle maps and that no independent comparison re-choice remains.
- Step 3: checked the boundary/cycle factorization against `015I`; the cited compatibility statements provide the commuting factors.
- Step 4: checked totalization and the second-degree filtration against `015K` and the total-complex definition; the corrected bounds make each total sum finite.
- New exact-source horseshoe node: checked self-contained hypotheses, TeX, target horseshoe reference, recorded searches, and concentrated-degree cases.
- Deleted the false comparison node, added the exact-source horseshoe node with this item as `created.item`, and repaired the induction maps.
- Removed the `lem-sp-cartan-eilenberg-properties` citations: its Grothendieck and enough-injectives hypotheses are not assumed by this item; the item's six explicit CE clauses supply the needed row facts.
- Removed the direct item dependency on the ordinary horseshoe-lift node; the exact-source node is the only cited middle-lift interface, and its own statement cites the ordinary target horseshoe construction.
