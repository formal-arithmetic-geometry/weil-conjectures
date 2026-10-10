# Stage 1 report

1. Files written:
   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-open-subscheme-fpqc-descent.json` — statement item, no Mathlib match; split into five proof steps.
   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-fpqc-affine-standard-refinement.json` — statement-only node, no Mathlib match.
   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-standard-fpqc-quotient-topology.json` — statement-only node, Mathlib has only the one-morphism generalization `Flat.isQuotientMap_of_surjective`.

2. Attachments: `lem-weil-pbc-fibre-product-points` is the existing Mathlib leaf used for the fibre-product point argument.

3. WANTED: none.

4. The imported item had the exact Tag 03N0 statement but no proof. I read `descent.tex`, the proof of `lemma-open-fpqc-covering` (Tag 03N0), including its use of `lemma-equiv-fibre-product` (Tag 02KI), the affine standard-refinement clause from the fpqc definition (Tag 022B), and `morphisms-lemma-fpqc-quotient-topology` (Tag 02JY). The existing DAG node `lem-weil-pbc-fibre-product-points` states the point description needed for the set-theoretic descent step, so I did not create a duplicate. No Lean declaration in either source checkout carries this blueprint tag or states the item.

## Review by H1

I checked the item hypotheses against Tag 03N0: the family is an fpqc covering, the $W_i$ are opens, and pairwise pullbacks agree. Step 1 uses the existing fibre-product-points statement to justify the equivalence relation on points and uses the fpqc definition only for joint surjectivity; the resulting subset is $W=\bigcup_i g_i(W_i)$. Step 2 is the elementary affine-locality of openness. Step 3 uses the new affine-standard-refinement statement exactly for the finite affine refinement supplied by the fpqc definition, and records the pullback equality along each refinement map. Step 4 uses the new quotient-topology statement to make the descended subset open. Step 5 records uniqueness from joint surjectivity and the restricted structure sheaf. I tested the identity cover and a singleton faithfully flat affine cover: the construction returns the original open and uniqueness is immediate. I ran the required LeanFinder, Loogle, and Mathlib-grep searches for both new nodes; no exact family-level declaration was found. The Mathlib one-morphism quotient-map result was recorded as a generalization only because it does not state the finite-family construction.

## Not duplicates

`lem-weil-pbc-fpqc-affine-standard-refinement` vs existing `lem-galois-fpqc-singleton-affine-refinement`: the existing node handles a singleton fpqc morphism and constructs a finite affine refinement of its source; the new node handles an arbitrary fpqc family over an affine base and a standard faithfully-flat finite family refining it.

`lem-weil-pbc-fpqc-affine-standard-refinement` vs existing `lem-pc-field-extension-fpqc-cover`: the existing node states that a field extension gives an fpqc singleton; the new node extracts a finite standard affine refinement from an arbitrary fpqc family.

`lem-weil-pbc-fpqc-affine-standard-refinement` vs existing `def-weil-pbc-fpqc-covering`: the definition gives the finite affine-image condition for an fpqc family; the new node packages that condition as a finite standard faithfully-flat refinement over an affine base.

`lem-weil-pbc-fpqc-affine-standard-refinement` vs existing `lem-pc-fpqc-descent`: the existing node proves descent of quasi-coherent modules; the new node only supplies the affine standard-cover refinement used for open subsets.

`lem-weil-pbc-fpqc-affine-standard-refinement` vs existing `lem-weil-pbc-fpqc-local-on-base-criterion`: the existing node is a criterion for properties local on the base; the new node is the covering refinement fact used before applying a quotient-topology lemma.

`lem-weil-pbc-fpqc-affine-standard-refinement` vs existing `lem-weil-pbc-etale-open-fpqc-descent`: the existing node descends opens after base change to an etale scheme and cites Tag 03N0; the new node is the affine refinement ingredient inside Tag 03N0 itself.

`lem-weil-pbc-standard-fpqc-quotient-topology` vs existing `lem-weil-pbc-fpqc-descend-universally-closed`: the existing node descends universal closedness of a morphism; the new node proves openness of a subset from its inverse images under a finite standard affine fpqc family.

lem-weil-pbc-fpqc-affine-standard-refinement vs lem-weil-pbc-open-subscheme-fpqc-descent: the item concludes existence and uniqueness of an open subscheme, while this node only extracts the finite standard affine refinement used in the openness proof.

`lem-weil-pbc-standard-fpqc-quotient-topology` vs existing `lem-galois-fpqc-descend-open-immersion`: the existing node descends the property of being an open immersion for a morphism; the new node concerns openness of an underlying subset under a finite standard fpqc family and supplies the quotient-topology implication used by Tag 03N0.

## Second reading by H1

- Item statement: checked against Descent Lemma Tag 03N0 (`lemma-open-fpqc-covering`) hypothesis by hypothesis; verdict: agrees.
- Step 1: checked against the statement of `lem-weil-pbc-fibre-product-points`, the fpqc definition Tag 022B, and the first paragraph of Tag 03N0; verdict: cited facts support the set-theoretic descent and joint-surjectivity claims.
- Step 2: checked against the Zariski-local openness argument in Tag 03N0; verdict: elementary and correct.
- Step 3: checked against the affine refinement paragraph of Tag 03N0 and the repaired refinement node; verdict: pullback of the equality gives open inverse images as stated.
- Step 4: checked against Morphisms Lemma Tag 02JY and the final paragraph of Tag 03N0; verdict: the quotient-topology implication is the required conclusion.
- Step 5: checked against joint surjectivity in Definition Tag 022B and the uniqueness clause of Tag 03N0; verdict: correct, with restricted structure sheaf uniqueness elementary.
- `lem-weil-pbc-fpqc-affine-standard-refinement`: checked against Definition Tag 022B and the affine-refinement passage in Tag 03N0; verdict: self-contained after explicitly citing faithful-flat ring maps.
- `lem-weil-pbc-standard-fpqc-quotient-topology`: checked against Morphisms Lemma Tag 02JY applied to the finite coproduct; verdict: self-contained after replacing the undefined “standard fpqc” shorthand by its faithful-flat ring-map condition.
- Small cases checked: identity cover, singleton faithfully flat affine cover, empty affine base, and a singleton family; all statements behave as expected.
- Changes: removed undefined “standard fpqc covering” terminology from both auxiliary statements, added `def-weil-pbc-faithfully-flat-ring-map` dependencies, and updated the source wording and this review.
