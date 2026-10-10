Files written:

- `dag/nodes/sec-picard-framework/lem-sc-p1-right-derived-triangle-connecting.json`: repaired four-step proof.
- `dag/nodes/sec-picard-framework/lem-weil-pbc-degreewise-split-derived-triangle.json`: new statement-only child; Mathlib search found the degreewise-split triangle API but no exact project leaf.
- `dag/nodes/sec-picard-framework/lem-weil-pbc-complex-ses-connecting-formula.json`: new statement-only child; Mathlib has only the abstract snake connecting map.
- `citations.json`: verbatim quotes for every step citation.

Attachments: none. No sorry-free declaration states the full horseshoe-to-derived-triangle comparison.

WANTED: none.

The returned version used universality of delta-functors to identify the two connecting maps. That is insufficient because reversing the sign of every connecting map preserves universality and degree zero. I removed that argument. The repaired route fixes the sign directly: a horseshoe resolution is degreewise split, its connecting chain map is `pi d s`, the split triangle is identified with the cone triangle whose third map is `-p`, and the resolution quasi-isomorphisms transport this specific triangle to the triangle of the original short exact sequence. Only after this comparison is the right derived functor applied.

## Review by F1

 I read the item source (Stacks derived Tags 05TE and 015B), the cone convention in Tag 014Q, and Homology Tags 011J and 0117. I also opened every cited DAG node. Step 1 uses the existing horseshoe statement for existence and degreewise exactness, the injective-resolution SES for splittings, the degreewise-split connecting lemma for `pi d s`, and the complex long-exact node for the homology maps; each cited statement says exactly those facts. Step 2 uses the new split-triangle statement and the new connecting-formula statement, together with the derived-category definition that distinguished triangles are cone triangles with third map `-p`; these fix the sign and identify the snake map on cocycles. Step 3 uses the injective-resolution-of-complexes statement for the three quasi-isomorphisms, the complex-SES triangle naturality statement, the cone convention, and the short-exact-sequence triangle statement for the target triangle. Step 4 uses bounded-below injectives are K-injective, triangulatedness of `Rv`, the cohomology long exact sequence, and the canonical `H^n(Rv(X[0]))` to `R^n v(X)` isomorphisms. No step invokes universality, so the sign ambiguity in the returned proof is gone.

I checked the hypotheses at each use: the abelian and enough-injectives assumptions come from the item and the horseshoe nodes; bounded-below injective terms are supplied by the horseshoe; degreewise splittings use injectivity of `I_A^n`; the quasi-isomorphism comparison is for the same short exact sequence `S`; and the termwise application of `v` is the construction of the right derived functor on these K-injective representatives. The zero short exact sequence gives zero maps in both descriptions, and the degree-zero case reduces to the ordinary exact sequence under `R^0v = v`. Both new statements are intentionally unsplit because they are used as standalone lemmas; their Mathlib searches and blueprint provenance are recorded in their node files.

## Not duplicates

`lem-weil-pbc-degreewise-split-derived-triangle` vs `lem-sf-derived-ses-triangle`: the former concerns arbitrary degreewise split short exact sequences of complexes and fixes the `pi d s` sign; the latter concerns objects concentrated in degree zero and only asserts existence of a triangle.

`lem-weil-pbc-degreewise-split-derived-triangle` vs `def-weil-abstract-derived-category`: the existing definition states which cone triangles are distinguished and their `-p` convention; the new lemma proves that a degreewise split short exact sequence is isomorphic to that cone triangle and identifies its third map as `pi d s`.

`lem-weil-pbc-complex-ses-connecting-formula` vs `lem-weil-pbc-complex-ses-homology-long-exact`: the former gives the cocycle formula for the connecting map; the latter asserts only existence and exactness of the long sequence.
`lem-weil-pbc-complex-ses-connecting-formula` vs `lem-weil-pbc-complex-ses-long-exact-naturality`: the latter transports already-given connecting maps between two sequences; it does not identify either map with the explicit cocycle representative.
`lem-weil-pbc-complex-ses-connecting-formula` vs `lem-weil-pbc-degreewise-split-connecting-morphism`: the latter constructs the chain map `pi d s`; the new node additionally identifies its induced cohomology map with the long-exact connecting morphism.
`lem-weil-pbc-complex-ses-connecting-formula` vs `lem-weil-pbc-horseshoe-delta-functor`: the latter defines horseshoe connecting maps and their naturality abstractly; it does not state the split-complex cocycle formula.

## Second reading by F1

- Item statement: checked against Derived Tags 05TE and 015B; hypotheses and the canonical-identification conclusion agree.
- Step 1: checked against the horseshoe, injective-resolution SES, degreewise-split map, and complex long-exact statements; every cited statement supplies the stated construction.
- Step 2: checked against Derived Tags 014I/014Q and Homology Tag 011J; the split triangle and explicit `pi d s` formula fix the sign.
- Step 3: checked against the injective-resolution SES-complexes and complex-SES triangle naturality nodes; the resolution maps give the required triangle morphism.
- Step 4: checked against the K-injective, triangulated-derived-functor, homology-long-exact, and single-object identification nodes; all bounded-below hypotheses are present.
- `lem-weil-pbc-degreewise-split-derived-triangle`: statement-only, self-contained, definitions cited, source corrected to Tags 014I/014Q, no exact existing statement with the explicit split formula.
- `lem-weil-pbc-complex-ses-connecting-formula`: statement-only, self-contained, source corrected from the incorrect 0119 citation to 011J plus 0117; no duplicate because the existing long-exact node omits the cocycle formula.

Changes: corrected the item `created.item`; removed the stale universal-delta proof dependency; corrected the Homology tag citations; added the existing complex-SES triangle naturality dependency and citation to Step 3.
