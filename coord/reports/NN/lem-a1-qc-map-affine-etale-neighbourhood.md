# Worker report

## Files written

- `lem-a1-qc-map-affine-etale-neighbourhood` — statement node, split; no Mathlib match.
- `lem-a1-space-affine-etale-cover` — statement-only supporting node, unsplit; no Mathlib match.
- `lem-a1-space-fibre-product-point` — statement-only supporting node, unsplit; no Mathlib match.
- `lem-a1-separated-etale-chart` — statement-only supporting node, unsplit; no Mathlib match.
- `citations.json` and the recorded Mathlib search logs were written for the item and each new node.

## Attachments

None. I searched the project declarations in `WeilConjectures/` and `Comparator/` by the item id, the algebraic-space and affine-etale keywords, and the imported upstream names; no sorry-free declaration states this item or any of the three new supporting statements exactly.

## WANTED

None. The Stacks Project source used here is present locally.

## What was wrong or incomplete

The imported item had an empty proof even though its statement is the affine-etale neighbourhood assertion in Stacks Tag 0APL. I split the proof into four steps. The first step needs a single affine chart over the quasi-compact image, so I added `lem-a1-space-affine-etale-cover`; the pointwise surjectivity argument in Tag 03H4 is a separate supporting statement, `lem-a1-space-fibre-product-point`; and separatedness of the chart pullback is `lem-a1-separated-etale-chart`. The existing node `lem-a1-etale-space-locally-quasi-finite` supplies the final locally-quasi-finite conclusion. No hypothesis or conclusion of the imported item was changed.

## Not duplicates

- `lem-a1-space-affine-etale-cover` vs `lem-trf-space-fibre-products-etale-covers`: the new node gives an affine disjoint-union etale atlas and openness of chart images; the existing node concerns fibre products of an already-given covering family.
- `lem-a1-space-fibre-product-point` vs `lem-trf-space-fibre-products-etale-covers`: the new node is the pointwise common-field lifting criterion for one scheme fibre product; the existing node is a family-level pullback/sheaf construction.
- `lem-a1-separated-etale-chart` vs `lem-a1-etale-space-locally-quasi-finite`: the new node proves separatedness for a separated scheme chart and its scheme base changes; the existing node proves local quasi-finiteness of an etale algebraic-space morphism.

## Review by NN

I read the item source in `literature/stacks-project/spaces-properties.tex`, Tag 0APL (the proposition `proposition-sheaf-fpqc`), together with Tags 03FX (`lemma-cover-by-union-affines`), 03BX (`lemma-topology-points`), 03H6 (`lemma-quasi-compact-affine-cover`), 03H4 (`lemma-points-cartesian`), 03FZ (`lemma-separated-cover`), and 03WS (`lemma-etale-locally-quasi-finite`). The item statement retains its hypotheses that S is a scheme, E is an algebraic space over S, and C is quasi-compact over S, and retains the represented scheme fibre product and all four properties of its projection. The new nodes state only the smaller atlas, point-lifting, and separatedness facts used by the proof; each introduces all of its schemes, maps, and hypotheses.

Step 1 uses the atlas and open-image clauses of `lem-a1-space-affine-etale-cover`, the definition of quasi-compact scheme in `def-weil-pbc-quasi-compact-scheme`, the finite affine coproduct identification in `lem-weil-pbc-finite-affine-coproduct-spectrum`, the scheme coproduct universal property in `lem-weil-pbc-scheme-coproduct-family`, and the representable-etale/sheaf formulation in `def-trf-algebraic-space`. These statements say respectively that the components cover E with open images, a quasi-compact image has a finite subcover, the finite disjoint union is affine, component maps glue, and the glued map remains representable etale. The continuous image of a quasi-compact space is quasi-compact and selecting a finite subcover are the elementary topological part of this step.

Step 2 uses the representability clause of `def-trf-algebraic-space`, the chartwise etale definition in `def-weil-etale-morphism`, and the exact common-field point-lifting and surjectivity conclusion of `lem-a1-space-fibre-product-point`. I checked that the latter has the same S, E, C, U, c, and u hypotheses and concludes surjectivity of the scheme fibre product projection. No separatedness or quasi-compactness of E was introduced.

Step 3 applies `lem-a1-separated-etale-chart` to the affine (hence separated) U from step 1. Its statement explicitly gives representable separatedness of u and separatedness of every scheme base change, so it supplies the separatedness of V to C without assuming E or S separated.

Step 4 applies the existing `lem-a1-etale-space-locally-quasi-finite` to the etale map V to C. The node's chartwise hypothesis is met because step 2 identifies V as a scheme and its map to C as etale; its conclusion is exactly locally quasi-finite. The item does not assert quasi-compactness of V to C.

For the new nodes I searched the whole DAG and blueprint for the Stacks tags, algebraic-space keywords, and the corresponding pullback/etale/separated notions before creating them. Each node has all three required search kinds (LeanFinder or Loogle, grep, and LeanSearch) recorded under its final id; the hits were scheme-only or the service reported an unknown identifier, so none is a Mathlib leaf. I tested the statements on the empty C case, a one-point affine C mapping to an affine E, a single affine chart, and a finite disjoint union of two affine charts. These cases expose no missing nonemptiness, separatedness, or quasi-compactness hypotheses. I also verified every citation quote is copied verbatim from the cited node statement, every step use is included in `proof_deps`, and the server `check_dag` passed before this report was written.

## What remains unfinished

Nothing for this stage-1 split.

Additional duplicate-tag audit pairs required by the delivery checker:

- `lem-a1-separated-etale-chart` vs `lem-a1-qc-map-affine-etale-neighbourhood`: the helper isolates separatedness of a separated scheme chart and its arbitrary scheme base changes; the item asserts existence of an affine chart whose pullback is also surjective, etale, and locally quasi-finite.
- `lem-a1-separated-etale-chart` vs `lem-sc-constant-locus-closed`: the helper is a base-change separatedness theorem for algebraic-space charts; the existing node is closedness of a constant locus.
- `lem-a1-separated-etale-chart` vs `lem-weil-pbc-etale-morphism-open-map`: the helper concerns separated diagonals over algebraic spaces; the existing node concerns openness of an etale morphism with scheme target.
- `lem-a1-separated-etale-chart` vs `lem-sbc-finite-etale-generic-fibre-cover-density`: the helper is chart separatedness; the existing node is density of a finite-etale generic-fibre cover.
- `lem-a1-separated-etale-chart` vs `lem-sbc-finite-etale-generic-fibre-hom-extension-existence`: the helper is chart separatedness; the existing node is extension of generic-fibre homomorphisms.
- `lem-a1-separated-etale-chart` vs `lem-sbc-flat-quasi-finite-smooth-local-dimension`: the helper is chart separatedness; the existing node concerns local dimension for flat quasi-finite smooth morphisms.
- `lem-a1-separated-etale-chart` vs `lem-sbc-generic-closed-subset-fibre-nonempty`: the helper is chart separatedness; the existing node asserts nonempty fibres over a generic closed subset.
- `lem-a1-separated-etale-chart` vs `lem-sbc-generic-fibre-incidence-spread`: the helper is chart separatedness; the existing node spreads generic-fibre incidence data.
- `lem-a1-separated-etale-chart` vs `lem-sbc-geometric-generic-cover-spread`: the helper is chart separatedness; the existing node spreads a geometric generic cover.
- `lem-a1-separated-etale-chart` vs `lem-sbc-smooth-connected-generic-geometry-core`: the helper is chart separatedness; the existing node constructs a smooth connected generic geometry core.
- `lem-a1-separated-etale-chart` vs `lem-sbc-smooth-connected-generic-geometry-stalk-iso`: the helper is chart separatedness; the existing node proves a stalk isomorphism in smooth connected generic geometry.
- `lem-a1-separated-etale-chart` vs `lem-sbc-smooth-connected-generic-geometry`: the helper is chart separatedness; the existing node states the full smooth connected generic geometry package.
- `lem-a1-space-affine-etale-cover` vs `lem-a1-qc-map-affine-etale-neighbourhood`: the helper supplies the atlas and open-image construction used in step 1; the item additionally selects finitely many components and proves the four properties of the pullback.
