# Stage-1 report

1. Files written: `dag/nodes/sec-picard-framework/lem-pc-section-cohomology-untwisted-comparisons.json` (repaired item); `def-pc-section-cohomology-presheaf.json` (new definition); `def-pc-restricted-resolution-sections.json` (new definition). `citations.json` records verbatim statements for every dependency used by every proof step.
2. Attachments: none. No sorry-free declaration matching the item was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or the upstream reference.
3. WANTED: none.
4. The return identified four faults. The item had routed through `def-weil-pbc-flat-base-change-open-choices`, whose statement does not define the raw section presheaf or the restricted-resolution bundle; I added precise same-unit definition nodes and replaced that off-unit dependency. The old second step repeated the first step, so it now derives the restriction square, defines the two inverse additive equivalences, and rewrites the square. The old third step said “transport” without the required square; it now displays coefficient/restriction naturality and combines it with the scalar-core and restriction equations. The item statement and hypotheses remain unchanged.

## Review by NK

I read the item against Tags 01E4 (Lemma 20.7.3) and 01E1 (Lemma 20.7.1), and read the full statements of the existing comparison, restriction-naturality, scalar-core, restricted-resolution-existence, and open-module-cohomology nodes. Step 1 uses restricted-resolution existence to choose the pinned data and uses the new presheaf definition and comparison-map statement to obtain exactly the top additive comparison. Step 2 uses the restriction-naturality statement under precisely V≤W and the image equality; its displayed equation supplies d, and the inverse rewrites give e and t. Step 3 uses the scalar-core statement at n=1, then the coefficient-functor naturality supplied by open-module cohomology to write the restriction square explicitly; substitution into the restriction equation yields the scalar formula on U. Every cited statement says the object or equation used, and all citation quotes are verbatim in `citations.json`.

For the new definitions I searched the whole DAG and blueprint (`blueprint_refs.py search`); no existing node states either notion. LeanFinder, Loogle, grep, and LeanSearch were run for each. Mathlib has only a generic sheaf cohomology presheaf, not this module section-complex presheaf, and no restricted-resolution bundle. I checked edge cases q=0, empty opens, zero modules, and identity morphisms: the definitions and quantified equations remain meaningful and impose no extra hypotheses. The repair removes the route mismatch, avoids a restatement step, and records the scalar/restriction square required by E5.

Dry run: `deliver.py NK lem-pc-section-cohomology-untwisted-comparisons --no-push` was run after repair.

## Not duplicates

def-pc-restricted-resolution-sections vs lem-pc-higher-direct-image-affine-cohomology-presentation: the existing node compares natural transformations on affine opens and uniqueness of maps, while the new definition packages a restricted injective resolution and its section-complex isomorphism.
def-pc-restricted-resolution-sections vs lem-pc-open-restriction-module-cohomology: the existing node identifies module cohomology after restricting to an open, while the new definition records a chosen restricted injective resolution and pinned section comparison.
def-pc-restricted-resolution-sections vs lem-pc-sections-open-base-change: the existing node is a higher-direct-image open-base-change isomorphism, while the new definition concerns termwise injective resolutions and section complexes.
def-pc-restricted-resolution-sections vs lem-sc-affine-basis-restricted-lower-tail-local-bound: the existing node is a vanishing/local-basis assertion for a truncated complex, while the new definition is resolution data.
def-pc-restricted-resolution-sections vs new-qcoh-inverse-affine-open-vanishing: the existing node is vanishing of open cohomology under qcqs hypotheses, while the new definition constructs restricted resolutions.
def-pc-restricted-resolution-sections vs lem-sc-affine-basis-restricted-lower-tail-local-bound-aux: the existing node proves a specific lower-tail vanishing, while the new definition records resolution restriction and section comparison.
def-pc-restricted-resolution-sections vs lem-pc-higher-direct-image-affine-basis-vanishing: the existing node turns affine-open cohomology vanishing into a direct-image vanishing, while the new definition is restricted-resolution bookkeeping.
def-pc-section-cohomology-presheaf vs lem-pc-higher-direct-image-affine-cohomology-presentation: the existing node states coefficient naturality and affine detection for higher direct images, while the new definition defines raw section-complex homology values and restriction maps.
def-pc-section-cohomology-presheaf vs lem-pc-open-restriction-module-cohomology: the existing node identifies derived module cohomology after open restriction, while the new definition is the presheaf of homology of a specified section complex.
def-pc-section-cohomology-presheaf vs lem-pc-sections-open-base-change: the existing node is a base-change theorem for higher direct images, while the new definition constructs the raw section-cohomology presheaf.
def-pc-section-cohomology-presheaf vs lem-sc-affine-basis-restricted-lower-tail-local-bound: the existing node is a local vanishing bound, while the new definition gives values and restriction maps of section-complex homology.
def-pc-section-cohomology-presheaf vs new-qcoh-inverse-affine-open-vanishing: the existing node is a qcqs vanishing theorem, while the new definition is an unrestricted construction of a presheaf.
def-pc-section-cohomology-presheaf vs lem-sc-affine-basis-restricted-lower-tail-local-bound-aux: the existing node proves vanishing for one truncated complex, while the new definition defines all section-complex homology presheaf maps.
def-pc-section-cohomology-presheaf vs lem-pc-higher-direct-image-affine-basis-vanishing: the existing node is an implication from affine cohomology vanishing to direct-image vanishing, while the new definition is raw presheaf construction.
def-pc-restricted-resolution-sections vs lem-pc-section-cohomology-unit-comparisons: the existing item uses restricted data but does not define its structure; this node defines the data.
def-pc-restricted-resolution-sections vs lem-pc-resolution-unit-twist-comparison: the existing theorem constructs unit-twist comparisons, while this node defines the underlying restricted-resolution record.
def-pc-restricted-resolution-sections vs lem-pc-resolution-open-restriction-natural: the existing theorem assumes a restricted-resolution argument and proves a restriction comparison; this node defines that argument.
def-pc-restricted-resolution-sections vs lem-pc-resolution-open-restriction-core: the existing theorem proves a special scalar-open restriction result and assumes restricted data; this node defines the data.
def-pc-section-cohomology-presheaf vs lem-pc-section-cohomology-unit-comparisons: the existing item uses the presheaf as an input and proves comparisons, while this node defines its values and maps.
def-pc-section-cohomology-presheaf vs lem-pc-resolution-unit-twist-comparison: the existing theorem uses raw section cohomology in a unit-twist comparison, while this node defines the raw presheaf.
def-pc-section-cohomology-presheaf vs lem-pc-resolution-open-restriction-natural: the existing theorem assumes the presheaf and proves a restriction square, while this node defines the presheaf.
def-pc-section-cohomology-presheaf vs lem-pc-resolution-open-restriction-core: the existing theorem assumes the presheaf and proves a special restriction result, while this node defines it.

## Second reading by NK

- Item statement: checked against Stacks Tags 01E4 (Lemma 20.7.3) and 01E1 (Lemma 20.7.1), including arbitrary morphism, open inclusions, unrestricted q, scalar action, and absence of finiteness assumptions; verdict: hypotheses and clauses agree.
- Step 1: checked each cited statement (restricted-resolution existence, section presheaf, restricted data, and comparison map) verbatim in `citations.json`; verdict: these provide exactly the chosen data and top comparison, with no hidden base-change assumption.
- Step 2: checked restriction-naturality, comparison, presheaf, and open-cohomology statements; verdict: the supplied square has the required domain/codomain and inversion yields both additive equivalences and restriction commutation.
- Step 3: checked scalar-core, restriction-naturality, comparison, presheaf, restricted data, and coefficient-cohomology statements; verdict: the explicit coefficient/restriction naturality square and n=1 scalar identity justify the transported scalar formula, including nonunits.
- New node `def-pc-section-cohomology-presheaf`: checked self-contained notions and edge cases q=0, empty opens, and zero complexes; searched DAG/blueprint and Mathlib; verdict: distinct definition, statement only, no hollow data.
- New node `def-pc-restricted-resolution-sections`: checked self-contained scheme/module/resolution/open data and zero/identity restriction cases; searched DAG/blueprint and Mathlib; verdict: distinct definition, statement only, no hollow data.

Changes made in this second reading: retained the repaired same-unit definition route and explicit restriction/scalar square; added this hypothesis-by-hypothesis review record and verified citation/search metadata before delivery.
