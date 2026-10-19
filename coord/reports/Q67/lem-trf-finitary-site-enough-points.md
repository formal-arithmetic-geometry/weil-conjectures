# Worker report: lem-trf-finitary-site-enough-points

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-finitary-site-enough-points.json` — repaired item split; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-point-system-refine.json` — statement-only support node; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-point-system-refine-all.json` — statement-only support node; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-inverse-system-site-point.json` — statement-only support node; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-point-family-conservative.json` — statement-only support node; no Mathlib match.
- `citations.json` — repaired verbatim quotes for every citation.

## Attachments

None. No sorry-free project declaration states the item or a newly created support statement exactly.

## WANTED:

None. The Stacks source is present at `literature/stacks-project/sites.tex`.

## What was wrong or corrected

The returned delivery identified C4/E5 in the point-system argument, E1/E3 in the set-indexing argument, and B2/B3/B5/F1/F2/F4 in the schema, tags, and unsupported review claims. I corrected all of them. The support statements now introduce the directed index posets, transition maps, colimits, refinement inclusion, stalk notation, and covering-lifting quantifiers explicitly. Their sources use the actual Stacks tags: 00YO for `lemma-refine`, 00YP for `lemma-refine-all-at-once`, 00YC for `proposition-point-limits`, 00YA for `lemma-point-site-topos`, and 00YK/00YM for the enough-points criterion.

## Review by Q67

I reread the item and all four support statements against `literature/stacks-project/sites.tex`, especially the complete proofs at Tags 00YO, 00YP, 00YC, 00YA, 00YK, 00YM and 00YQ. Step 1 now uses the statements of both refinement nodes: the one-cover lemma is applied at each stage to the current representative, and every element of the final colimit is represented at a stage, so its lifting task is handled later and persists under further refinement. This supplies the argument missing from the prior all-at-once citation. Step 2 uses the inverse-system point statement only for its stated finite-limit and covering-surjectivity criterion, then explicitly refines an arbitrary cover to a finite cover and composes the resulting lift; it also records the two selected section images as colimit classes. Step 3 uses the fixed `\mathcal U\in\mathcal V` convention to justify that the chosen-skeleton sheaves, objects, and section pairs form a set in `\mathcal V`; it then applies the support node's explicit stalk-class criterion. I checked all hypotheses: the initial system is nonempty, finite limits are assumed by the item, finite-cover refinement is used exactly once in Step 2, and the chosen family is indexed by a set. I updated `citations.json` so every quote is verbatim from the current cited statement. I reran the Mathlib searches for every statement whose wording changed; all searches found only generic site-point infrastructure and no exact criterion.

## Not duplicates

- `lem-trf-inverse-system-site-point` vs `lem-trf-site-point-reconstruction-sets`: the existing node reconstructs a cofiltered neighbourhood category from an already given geometric topos point, while the new node starts with a concrete inverse system satisfying finite-limit and covering-surjectivity conditions and constructs a point.
- `lem-trf-point-system-refine` vs `lem-trf-finitary-site-enough-points`: the support node refines one fixed inverse-system element and one finite cover; the item constructs a conservative family for all sheaves and section pairs.
- `lem-trf-point-system-refine-all` vs `lem-trf-finitary-site-enough-points`: the support node refines one fixed pair of stalk sections and all finite-cover tasks; the item concludes existence of enough points.
- `lem-trf-point-family-conservative` vs `lem-trf-finitary-site-enough-points`: the support node is a criterion for an already given family, while the item constructs the family.
- `lem-trf-inverse-system-site-point` vs `lem-trf-finitary-site-enough-points`: the support node constructs one geometric point from one explicit inverse system; the item constructs a set-indexed conservative family from arbitrary sheaf sections.
- `lem-trf-inverse-system-site-point` vs `lem-trf-site-point-fibre`: the existing fibre node starts with an already given site point and computes its fibre/stalk, whereas the new node starts with an inverse system and proves it defines a point.
- `lem-trf-inverse-system-site-point` vs `lem-trf-oriented-product-points-conservative`: the existing oriented-product node concludes conservativity for geometric points of a special oriented product; the new node is the general finite-limit site criterion used to construct each point.
- `lem-trf-point-family-conservative` vs `lem-galois-stalk-representable`: the existing node identifies a particular geometric stalk with a representable fibre; the new node proves the general section-separation criterion for an arbitrary family of points.
- `lem-trf-point-family-conservative` vs `lem-weil-pbc-sets-sheafification-geometric-stalk`: the existing node concerns one sheafification/stalk identification; the new node concerns joint reflection of isomorphisms by a family.
- `lem-trf-point-family-conservative` vs `lem-weil-pbc-sheafification-geometric-stalk`: the existing node identifies a single stalk construction; the new node proves conservativity from separation by stalk classes.
- `lem-trf-point-family-conservative` vs `lem-cbc-proetale-sheafification-geometric-stalk`: the existing node is a pro-étale sheafification comparison; the new node is an arbitrary-site family criterion.
- `lem-trf-point-family-conservative` vs `lem-fix-geometric-stalk-topos-point`: the existing node constructs/identifies a geometric stalk topos point; the new node tests a family of already given points for conservativity.
- `lem-trf-point-family-conservative` vs `lem-weil-proetale-constant-sheaf-stalk`: the existing node computes a constant-sheaf stalk; the new node concerns all sheaves and section pairs.
- `lem-trf-point-family-conservative` vs `lem-trf-site-point-fibre`: the existing node computes the fibre of one site point; the new node gives a criterion for a family to reflect sheaf isomorphisms.
- `lem-trf-point-family-conservative` vs `lem-coef-subdivision-face-poset-calculus`: the existing node is a subdivision face-poset calculation despite sharing Tag 00YM; the new node is the enough-points section-separation lemma.
- `lem-trf-point-system-refine-all` vs `lem-trf-oriented-product-points-conservative`: the existing node applies enough points to affine oriented-product slices; the new node is the underlying all-at-once inverse-system refinement construction.
- `lem-trf-point-system-refine` vs `lem-trf-oriented-product-points-conservative`: the existing node proves conservativity for an oriented product; the new node refines one inverse-system element for one finite cover while preserving two sections.
