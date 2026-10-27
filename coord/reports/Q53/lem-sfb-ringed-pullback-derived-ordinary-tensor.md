# Stage-1 report: lem-sfb-ringed-pullback-derived-ordinary-tensor

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-pullback-derived-ordinary-tensor.json`: statement split into five steps following the actual resolution diagram of Stacks 0FPH; no change to the equality or its hypotheses.
- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-derived-tensor-augmentation-naturality.json`: new statement-only prerequisite, unsplit, no Mathlib match. It supplies the natural derived-to-ordinary tensor augmentation and its normalization on K-flat resolutions; it contains no pullback assertion.
- `citations.json`: one verbatim statement excerpt for each of the 16 proof-step citations.

## Attachments

None. Searched all of `lean/WeilConjectures/` for the item tag and comparison notions. The related `AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorComparison_app_app_fac` and its two counit-expansion lemmas in `SixFunctors/ProEtale/FiniteCoefficient/Derived/TensorSheaf.lean:394,410,420` concern the fixed-coefficient pro-etale pullback, not arbitrary ringed-topos module pullback. They do not attach this item.

## WANTED

None.

## Audit findings and changes

The imported statement is well-typed and agrees with the entire diagram of Stacks 0FPH, `lemma-tensor-pull-compatibility`. I preserved it, adding only the explicit citation for the tensor-augmentation interface. The source's final sentence accidentally says “left hand side of the diagram” twice; the intended identification is clear from the two displayed diagrams and needs no mathematical correction.

One real missing prerequisite was naturality and resolution independence of the tensor augmentation. The statement of `lem-weil-pbc-site-derived-tensor-descent` gives the derived bifunctor and its K-flat comparison but does not explicitly give a natural transformation with target the *ordinary* total tensor on arbitrary complexes. The new node supplies this separate interface. It is not a restatement of the item: it has one ringed site, no morphism of topoi, no pullback comparison, and no pullback compatibility identity. Its resolution-independent natural transformation requires the K-flat resolution-category argument of the construction preceding 06YU, not a two-line consequence of the comparison isomorphism on K-flat pairs alone. The future split should construct the augmentation from the total-tensor maps of resolution augmentations and use common K-flat refinements to prove independence and naturality. This argument is recorded here rather than hidden in the statement-only node.

I did not use `lem-pc-kflat-tensor-product`: its statement is for ringed **spaces**, not general ringed sites. Instead I used the existing site-level `lem-pur-kflat-total-tensor-model`, which expressly covers unbounded complexes and flatness of the terms of their total. All off-unit statement inputs are declared as generic tools in `split_report.tool_uses`.

The item's inherited blueprint ancestry has `from.node: null`; `tools/blueprint_refs.py ancestor` reports exactly `None`. I retained that inherited ancestry and its full place and via chain, and used precisely that ancestor for the new node. I read the latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`. This is an auxiliary tensor-cup prerequisite in the inherited chain, not a change to the unit's alteration route or its theorem. Neither unit nor chapter files were changed.

## Mathlib and duplicate searches

The item has the inherited actual search results, plus fresh logged LeanFinder, Loogle, grep and LeanSearch queries. The new augmentation node has its own natural-language and Loogle searches, grep of Algebra/Homology and CategoryTheory/Functor/Derived, and a second semantic phrasing about lax monoidal localization. Every recorded query occurs literally in `searches.jsonl`. Both semantic services returned results; none was recorded as unavailable or a false no-hit. I read the hits: ordinary pullback composition, tensor-total constructions, projective Tor and Cartesian product comparisons concern different statements. Strong monoidal localization requires all inverted maps to be stable under tensoring, which does not hold for ordinary tensor with arbitrary non-flat complexes. It therefore does not specialize to this augmentation in one line.

DAG searches covered 0FPH, the derived-to-ordinary comparison, tensor augmentation and tensor/localization/counit names; blueprint searches covered `0FPH`, `derived-to-ordinary`, `tensor augmentation` and `tensor comparison`. No existing blueprint node states this general natural augmentation. The abstract `def-sf-kflat-tensor-presentation` assumes such a natural transformation as part of its data; it does not prove existence for the specified module-sheaf derived tensor. The scheme-specific cup realization and scalar-extension counit nodes do not state the general site bifunctor result.

## Not duplicates

lem-sfb-ringed-derived-tensor-augmentation-naturality vs lem-sfb-ringed-pullback-derived-ordinary-tensor: the new node constructs and normalizes the tensor augmentation on one arbitrary ringed site; the item proves compatibility with pullback between two ringed topoi.
lem-sfb-ringed-derived-tensor-augmentation-naturality vs lem-sfb-ringed-derived-naive-cup-comparison: the new node has no direct image or cup product; the existing node asserts the separate 0FPK cup comparison identity using these augmentations.
lem-sfb-ringed-derived-tensor-augmentation-naturality vs lem-weil-pbc-site-derived-tensor-descent: descent supplies a bifunctor on the derived categories and comparisons restricted to K-flat pairs, while the new node supplies the map to localized ordinary tensor on arbitrary complexes, including naturality when the maps are not quasi-isomorphisms.
lem-sfb-ringed-derived-tensor-augmentation-naturality vs def-sf-kflat-tensor-presentation: the existing definition packages an assumed natural transformation, while the new theorem asserts existence and normalization for the already selected ringed-site derived tensor.

## Review by Q53

I read Stacks `sites-cohomology.tex`, `lemma-tensor-pull-compatibility` (0FPH), both diagrams and the whole proof. I also read `lemma-K-flat-resolution` (06YS), `lemma-pullback-K-flat` (0G7E), `lemma-pullback-tensor-product` (07A4), `lemma-tensor-product-K-flat` (07A2), and the construction immediately before `definition-derived-tor` (06YU). These justify the actual resolution choices and the new augmentation statement; 0FPH is the source of the canonical horizontal arrows. No SGA route is used.

For step 1 I opened all four cited node statements. `lem-pc-kflat-resolution` gives actual augmentations, with flat terms, on any ringed site; `lem-pur-kflat-total-tensor-model` gives K-flatness and flat terms of the total on a site, without bounds; `lem-weil-pbc-ringed-pullback-preserves-kflat` applies to the general ringed-topos map and requires exactly the flat-term K-flat hypotheses we chose; and `lem-weil-pbc-ringed-topoi-derived-pullback` makes each comparison invertible. I explicitly avoided claiming that the map of ordinary totals is a quasi-isomorphism.

For step 2 I checked the new augmentation statement gives both invertibility on the chosen K-flat pair and the normalization with p,q. Thus e is genuinely invertible. The cited derived-pullback node expressly gives a natural transformation on all homotopy-category complexes, so its naturality applies to c even though c need not be a quasi-isomorphism. No computation of the derived pullback by the original, possibly non-flat total is assumed.

For step 3 I checked the statements of the tensor-pullback, projection-mate, pullback-preservation, tensor-augmentation and ordinary comparison nodes. The tensor-pullback node fixes computation by K-flat flat-term resolutions; the projection-mate node gives naturality of the same canonical mu used by the relative cup product. The comparison definition supplies the normalization, not a claim about an arbitrary monoidal structure. The displayed equation is its representative computation at P,Q; the two augmentation maps are the inverse representative isomorphisms. It is not the desired compatibility for arbitrary complexes asserted without proof.

Step 4 is an explicit substitution of the three naturality equations supplied by the cited statements: first mu at [p],[q], then alpha at p,q, then rho at f*p,f*q. Cancellation is only by Lf* of s, where s is an isomorphism in the derived category. Neither ordinary pulled-back augmentation has to be invertible. This is a short algebraic step, marked elementary with its interfaces cited.

For step 5 I opened the ordinary comparison definition and signed-total definition. The comparison is natural in module maps. On each (i,j) summand both routes have exactly the written scalar-insertion formula; there is no permutation and hence no extra Koszul sign. The same bidegree-preserving maps commute with the signed differential. Equality on direct-sum summands proves equality of the total maps; the final composition is with the explicitly defined theta. No stalk detection or enough-points hypothesis is being used.

I tested the new statement with zero complexes, zero cochain maps, identity maps, and K-flat inputs with identity augmentations. I also checked the non-flat one-point-site example R=Z and A=B=(Z/2)[0]: the derived tensor has a degree -1 Tor class and the augmentation kills it, so the statement correctly asserts a natural map rather than an isomorphism on arbitrary inputs. The pullback formula similarly allows the non-flat structural map Z to Z/2; the proof uses K-flat models, never flatness of that map. Unboundedness is handled by the cited site-level model result and direct-sum totals; no bounded convergence claim is invoked.

I checked B through E against these files: the one new node is self-contained, statement-only and independently smaller; all notions have existing definition interfaces or are introduced explicitly; citations quote actual statements; no circular dependency was introduced; and all steps are below 2000 characters. The only corrected draft choice was replacing the tempting space-only K-flat tensor citation by the general site-level model node and making the tensor augmentation's missing interface explicit.

## Unfinished work

None for this one-level split. The new statement-only augmentation node is left unsplit for the stage-1 queue, as required. Delivery remains subject to the maintainer's independent mathematical review.
