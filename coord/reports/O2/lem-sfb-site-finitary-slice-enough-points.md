## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-site-finitary-slice-enough-points.json`: statement, split into four proof steps; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement quotes for every cited node in each step.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree for the full item id and for the notions “finitary slice”, “enough points”, and the Tag 00YN criterion; no project declaration states this item without `sorry`. The existing declarations found concern other point criteria and do not cover the full slice-cover statement.

## WANTED:

None. The proof follows the Stacks source already present in `literature/stacks-project/sites.tex`.

## Findings and changes

The imported item was unsplit and had no proof. I retained its statement and hypotheses. The proof now applies the existing finite-cover enough-points theorem separately to each slice, transports the resulting points through the existing equivalence between sheaves on a localized site and the slice topos over the sheafified representable, and descends the resulting local isomorphisms along the assumed epimorphic coproduct. No new node was created: the finite-cover criterion, localized-site equivalence, geometric-morphism definition, sheaf axioms, and universe convention already exist. The statement is not a restatement of any cited node: it adds the family of slices and the epimorphic representable cover.

## Not duplicates

lem-sfb-site-finitary-slice-enough-points vs lem-trf-finitary-site-enough-points: the existing node assumes finite limits and finite refinements for the whole site, whereas this item assumes those conditions only on a set-indexed family of slices covered by representables.
lem-sfb-site-finitary-slice-enough-points vs lem-sfb-proetale-enough-points: the existing node is the pro-etale application with affine weakly-etale objects and proves its own slice hypotheses; this item is the generic criterion used by that application.
lem-sfb-site-finitary-slice-enough-points vs lem-weil-pbc-localized-sheaves-over-representable: the existing node is only the equivalence between a localized site and a topos slice; this item adds the enough-points conclusion from finite slice criteria and an epimorphic family.

## Review by N2

I read `coord/delivery-errors.md` sections B–E and checked the item against Stacks `sites.tex`, Tag 00YN (lemma-criterion-points), Proposition 00YQ, and the localized-site material around Tag 00Y1. I also read the full statements of `lem-trf-finitary-site-enough-points`, `lem-weil-pbc-localized-sheaves-over-representable`, `def-trf-geometric-morphism`, `def-weil-pbc-sites-and-cohomology`, and `def-weil-size-convention`. Step 1 uses exactly the existing whole-site criterion on each slice and the existing sheaf-slice equivalence; the transported inverse images preserve finite limits and have right adjoints because both ingredients do. Step 2 checks that the assumed conservativity on each slice applies to the restriction of the original morphism. Step 3 verifies the epimorphic-family descent directly from the sheaf equalizer condition, including injectivity, local surjectivity, and gluing on overlaps; this is the role of the representable coproduct hypothesis. Step 4 checks set-indexing using the fixed universe convention. I checked edge cases including an empty index family (where the epimorphism hypothesis cannot hold in a nondegenerate topos), a singleton cover, an empty slice, and identity morphisms. No statement was changed, no SGA source was cited, and no new node or cycle was introduced.

## Unfinished work

None.
