# Worker report: lem-trf-total-site-derived-components

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-total-site-derived-components.json`: item split into five proof steps; Mathlib searches found no match.
- `dag/nodes/sec-trace-formula/lem-trf-total-site-component-restriction.json`: statement-only supporting lemma; Mathlib searches found no match.
- `citations.json`: verbatim citation quotes for every node used by every item step.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its title, and the Stacks labels; no sorry-free declaration states this item.

## WANTED

None.

## What was wrong or corrected

The imported item had no proof and still had `status: unsplit`. Its statement is retained exactly. The imported `created` metadata records that it was seeded by Q55 as a child of the proper-hypercover delivery; this split is the direct Q119 delivery of that child. The existing `lem-trf-simplicial-derived-image-spectral-sequence` is a scheme/constant-module specialization and does not state the general small-site result, so it was not used as a citation. I searched the whole DAG and blueprint for Tags 09WG, 0D97, 0DH0, 09WF and the component-restriction terms; no duplicate supporting node exists. The only new node is the smaller exact/conservative component-restriction and injective-preservation lemma, which supplies the K-injective input while the item proof itself constructs the total morphism, derived comparison, inverse-image comparison, and unit compatibility.

## Not duplicates

- `lem-trf-total-site-component-restriction` vs `lem-trf-total-site-derived-components`: the supporting lemma proves the exact left adjoint formula, injective/K-injective preservation, and conservativity for the restriction functors but says nothing about any morphism $h$, derived direct images, inverse images, or derived units; the item combines those ingredients into the derived comparison and unit statement.
- `lem-trf-total-site-component-restriction` vs `lem-trf-simplicial-derived-image-spectral-sequence`: the new node is for arbitrary small simplicial sites and abelian sheaves and only establishes component restriction, its left adjoint, exactness, conservativity and injective preservation; the existing node is for simplicial schemes with constant modules and additionally proves an augmentation spectral sequence.
- `lem-trf-total-site-component-restriction` vs `def-trf-total-simplicial-etale-site`: the definition node constructs one total étale site for a simplicial scheme; the new statement concerns arbitrary sites and the exact component adjoint/injective consequence.

## What I could not finish

Nothing. No Lean files were written and no compiler or Lake command was run, as required for stage 1.

## Review by Q119

I read the item source in `literature/stacks-project/spaces-simplicial.tex`, including the component sheaf discussion preceding Tag 09WG, Tag 09WG (`lemma-restriction-to-components-site`), the following injective-component lemma, Tag 0DH0 (the componentwise morphism adjunction), and Tag 0D97 (`lemma-direct-image-morphism-simplicial-sites`). I also read the unit's chapter and unit records, the imported item, the existing specialized spectral-sequence node, all seven node statements cited by the item, the source of each new-node dependency, and the Mathlib search results recorded in `searches.jsonl`.

Step 1 uses the new component-restriction statement for the exact left adjoint, exact restrictions, and conservativity; it uses the site and simplicial-object definitions only to instantiate the total-site construction. I checked that the statement's finite coproduct formula has the correct direction `f_φ⁻¹G` and that the family detects isomorphisms degree by degree. Step 2 writes the total inverse image and direct image explicitly, with the transition map obtained by the component counit and the simplicial coherence map. The geometric-morphism definition supplies precisely the component adjunction and triangle identities used to prove the family adjunction; I checked the indices of `h_p`, `h_q`, `f_α`, and `f'_α` against the source's convention. Step 3 uses the bounded-below injective-representative statement and K-injective comparison statement; the new node supplies preservation of K-injectivity under each restriction. I checked that the representative is taken in the total abelian-sheaf category and that restricting it gives the component representative before applying `h_{n,*}`. Step 4 uses exactness of inverse images from the geometric-morphism definition and the derived-category definition; I checked that no derived inverse image is introduced because the termwise functor is exact. Step 5 uses the component units from Step 2, the derived K-injective comparison, and conservativity from Step 1. I checked that the claimed equality is the specified unit after the canonical comparison, rather than merely an abstract isomorphism of source and target.

For the new node I read the complete Tag 09WG statement and proof, including the explicit formula for `g_{n!}` and the subsequent injective-component lemma. Its hypotheses introduce the sites, simplicial structure and universe; its conclusion is strictly smaller than the item because it has no morphism `h`, no derived direct-image comparison, and no unit assertion. I tested the formula on the one-degree constant simplicial site (where the only summand is the identity) and on a two-degree diagram (where the finite coproduct has one summand for each order map). The Mathlib searches for the item and new node were run with LeanSearch, LeanFinder/Loogle and grep; all returned no declaration of the total simplicial-site result. The pre-existing item searches were read and reused.
