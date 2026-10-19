## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-point-support-fibre.json`: split item, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-etale-point-morphism-classification.json`: statement-only auxiliary, no Mathlib match.
- `citations.json`: verbatim statement quotes for every cited step.

## Attachments

No new Lean attachment. Existing statements used: `lem-trf-etale-topos-points-geometric`, `lem-weil-pbc-geometric-point-morphism-stalk-bijection`, and `lem-trf-family-common-extension-field`.

## WANTED

None.

## What was checked and corrected

The item source is the auxiliary fixed-support reduction used in the proof of Orgogozo Lemma 8.3.2 (printed p. 18), with Stacks Tags 04HU and 04FN supplying the geometric representatives and stalk transport. I searched the Lean source for the blueprint tag and for point-support terminology; no declaration states this item. I searched the DAG for the item, its Stacks tags, point-category terms, and residue-field support statements. The existing geometric-point reconstruction node and the geometric-point stalk-bijection node are genuinely more general tools and are cited rather than duplicated. The existing common-extension-field node supplies the field amalgamation needed for connectedness.

The new auxiliary node records the missing converse to Tag 04FN: natural transformations between the stalk point functors are uniquely induced by morphisms of geometric points, and are invertible because the induced stalk maps are bijective. I ran LeanFinder, Loogle, grep, and LeanSearch through `msearch.py` for both the item and this auxiliary; Mathlib only returned generic point Hom/sheaf-fiber and scheme-stalk APIs, so both remain non-Mathlib nodes. I checked all mathlib search records against the command logs.

Step 1 uses the existing reconstruction statement, the new converse classification statement, and the existing stalk-bijection statement; these say respectively that points have geometric representatives, 2-morphisms are classified by geometric-point maps, and the induced stalk map is bijective. Step 2 checks the residue-field factorization directly from the definitions of a geometric point and the canonical residue-field morphism; the converse support assertion is immediate. Step 3 uses the same classification and stalk-bijection statements to show that postcomposition preserves and reflects every Hom-set. Step 4 uses the existing common-extension-field statement to place the two residue fields in one common overfield, then uses the stalk-bijection and classification statements to obtain invertible 2-morphisms. The small cases of a point scheme and an algebraically closed residue field reduce to the identity stalk functor and were checked while auditing the argument. All cited hypotheses, including the common enlarged universe, are retained.

## Not duplicates

- `lem-trf-etale-point-morphism-classification` vs `lem-trf-etale-topos-points-geometric`: the former classifies morphisms and 2-cells between two represented points; the latter classifies objects only.
- `lem-trf-etale-point-morphism-classification` vs `lem-weil-pbc-geometric-point-morphism-stalk-bijection`: the former proves the converse uniqueness and 2-cell classification; the latter starts with a geometric-point morphism and proves its stalk map is bijective.
- `lem-trf-etale-point-support-fibre` vs `lem-trf-etale-topos-points-geometric`: the item fixes one scheme support and compares the residue-field point category, while the existing node concerns arbitrary points and has no support or full-faithfulness conclusion.

## Review by NS

I read the item node, the fixed-support source description, Stacks 04HU (the classification of small étale topos points), and 04FN (transport between geometric stalks). I also opened every cited node. The reconstruction node states that every topos point is represented by a geometric point and gives its stalk colimit. The stalk-bijection node states that a geometric-point morphism induces a unique bijective map on every étale stalk and that pointed-neighbourhood precomposition is an equivalence. The common-extension node states that any small family of field extensions embeds compatibly in one field. The new auxiliary states precisely the missing converse classification of natural transformations by geometric-point morphisms; it is strictly broader than the item because it has no fixed-support or residue-field restriction.

Step 1 uses exactly those three statements and checks the direction through the inverse-image/direct-image adjunction. Step 2 verifies, from the residue-field definition and the geometric-point definition, that a geometric representative over s factors through Spec κ(s), and that every such composite has support s. Step 3 checks that the same pointed-neighbourhood construction before and after postcomposition is the identity on the underlying étale scheme and therefore gives a bijection on every Hom-set; the hypotheses of the two stalk statements apply to both residue-field points. Step 4 uses the common-extension field for the two residue extensions over κ(s), then an algebraic closure and the stalk-bijection theorem to obtain invertible 2-morphisms; the auxiliary classification ensures these are the required unique point morphisms. The identity point and the case S = Spec κ(s) are the edge cases: all constructions reduce to the identity geometric stalk and the same argument applies.

I corrected the inherited item metadata by filling its blueprint place and replacing the empty proof with the four route steps. I added the auxiliary only after searches over the full DAG, blueprint, Lean source, and Mathlib; no existing node states the converse classification. The search records include LeanFinder, Loogle, grep, and LeanSearch for both nodes, with unavailable or nonmatching services recorded as such. Every citation quote in `citations.json` is a verbatim substring of its cited node statement.
- `lem-trf-etale-point-morphism-classification` vs `lem-galois-finite-stalks-comparison`: the existing node compares finite Galois stalks of a fixed sheaf, while the new node classifies all 2-morphisms between topos points.
- `lem-trf-etale-point-morphism-classification` vs `lem-weil-pbc-constructible-module-support-constructible`: the existing node proves constructibility of a module's support, while the new node concerns morphisms between geometric topos points.
- `lem-trf-etale-point-morphism-classification` vs `lem-weil-pbc-constructible-module-surjectivity-locus`: the existing node identifies a module surjectivity locus, while the new node classifies point morphisms.
- `lem-trf-etale-point-morphism-classification` vs `lem-weil-pbc-geometric-stalk-comparison-constant`: the existing node compares constant coefficient stalks, while the new node classifies all natural transformations of stalk functors.
- `lem-trf-etale-point-morphism-classification` vs `new-constructible-module-support-general`: the existing node concerns supports of constructible modules, while the new node concerns 2-cells of topos points.
- `lem-trf-etale-point-morphism-classification` vs `new-geometric-point-morphism-addcommgrp-stalk`: the existing node classifies additive-group stalk maps induced by a given geometric morphism, while the new node proves the converse classification for arbitrary topos 2-cells.
- `lem-trf-etale-point-morphism-classification` vs `new-geometric-point-morphism-category-equivalence`: the existing node proves equivalence of pointed-neighbourhood categories for a given field map, while the new node classifies every natural transformation and its invertibility.
- `lem-trf-etale-point-morphism-classification` vs `new-geometric-point-morphism-set-stalk`: the existing node gives uniqueness and bijectivity of a set-stalk map for a given field map, while the new node proves every point 2-cell arises uniquely this way.
- `lem-trf-etale-point-morphism-classification` vs `lem-weil-pbc-extension-by-zero-stalks`: the existing node computes extension-by-zero stalks, while the new node classifies morphisms of geometric points.
- `lem-trf-etale-point-morphism-classification` vs `lem-trf-affine-etale-split-neighbourhood`: the existing node splits an affine étale neighbourhood, while the new node classifies 2-morphisms between topos points.
- `lem-trf-etale-point-morphism-classification` vs `lem-trf-etale-point-support-fibre`: the new auxiliary classifies morphisms between arbitrary represented points; the item restricts to one support and proves residue-field full faithfulness and connectedness.
