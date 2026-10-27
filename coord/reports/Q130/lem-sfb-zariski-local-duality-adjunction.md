# Stage-1 delivery: lem-sfb-zariski-local-duality-adjunction

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-zariski-local-duality-adjunction.json: statement, split; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-direct-image-hom-open-ext.json: statement, unsplit; no Mathlib match. This is a comparison-map computation, without any adjunction hypothesis or invertibility conclusion.
- citations.json: verbatim statements for every node cited in every numbered step.

## Attachments

None. Searched lean/WeilConjectures by the item tag and by local duality, adjunction, trace and internal-Hom comparison. MixedHomDirectImageComparison.lean supplies an evaluation-mate transformation, not the local-to-global criterion or the open Ext action asserted by the new node. GlobalHomAdjunctionIso.lean and QCqsSheafRHomAdjunction.lean assume an existing adjoint and globally qcqs schemes, so do not attach to this item.

## WANTED

None.

## Findings and corrections

The statement is preserved. The source's sheafy trace is a morphism in the full module derived category: its source and target need not be quasi-coherent. Stacks duality.tex lemma-iso-on-RSheafHom explicitly requires a coherator for its general sheaf-level isomorphism assertion. We do not apply that assertion. We instead test our comparison on all affine neighbourhoods and in every integer degree. In particular no ordinary Hom sheaf gluing, no affine-intersection assertion, no bounded hypercohomology spectral sequence and no finite covering is used.

The source pointer equation-global-hom in the imported record is not the label of the relevant result in the local Stacks source. The result used as motivation is lemma-iso-global-hom, Tag 0B6I, whose proof identifies the map on global derived Hom. Its pre-existing global adjunction is not an input to our argument.

The blueprint ancestor tool prints None for this item, as in the existing record; new provenance retains that exact ancestor and prepends this item to via. The current blueprint's sk-thm-sf-ctf-stability-direct-images.proof.md step (3), and the imported provenance chain, locate this coherent-duality tool below the proper-image finiteness argument. No chapter or unit route is replaced. Whole-blueprint searches for sheafy, projection formula for internal, Zariski local, sheaf-rhom, internal-hom comparison, direct image Hom, and open Ext found no duplicate of this criterion or its supporting normalization computation.

## Not duplicates

lem-sfb-direct-image-hom-open-ext vs lem-pc-sheaf-rhom-projection-formula: the existing node supplies the canonical natural transformation only; the new node asserts its restriction compatibility and identifies its map on every open shifted Hom group. The existing node is a statement dependency, not replaced.
lem-sfb-direct-image-hom-open-ext vs lem-sc-mixed-hom-direct-image-comparison: the existing fixed-data mate equation concerns test objects and tensor-Hom transposition; it does not identify open hypercohomology with pushforward of arbitrary shifted morphisms.
lem-sfb-direct-image-hom-open-ext vs lem-sc-mixed-internal-hom-base-change-exchange: that node concerns a general base-change square and its internal-Hom exchange equation, not the action on open Ext groups.
lem-sfb-direct-image-hom-open-ext vs lem-trf-open-ext-hypercohomology-comparison: that node identifies open Ext with hypercohomology and handles naturality in its two arguments; it does not compute the direct-image internal-Hom comparison.
lem-sfb-direct-image-hom-open-ext vs lem-pc-global-hom-adjunction: that node proves a global isomorphism from an already supplied exceptional adjunction on qcqs schemes; our new node assumes no exceptional adjunction and asserts no isomorphism.

## Review by Q130

I read Stacks cohomology.tex Remark 0B69's definition by cup product and evaluation, Lemma 08DK's comparison of open hypercohomology with shifted derived Hom, Lemma 08DL on open restriction of internal Hom, Lemma 08FE on open restriction of derived direct image, and the proofs of 0D5W and 0D5X. I also read perfect.tex Lemma 08EU and its precise unbounded qcqs-morphism hypotheses, perfect.tex Lemma 08D5(1), and duality.tex equation-sheafy-trace and lemma-iso-global-hom. The latter motivate the map without supplying the criterion we prove.

For step 1 I opened each cited statement. The separated definition says the diagonal is a closed immersion; the quasi-separated definition asks exactly that this diagonal be quasi-compact. Over an affine open its inverse image is a closed subscheme, hence affine and quasi-compact. The two preservation statements explicitly allow arbitrary schemes and unbounded quasi-coherent complexes. The projection-formula statement requires only a qcqs morphism. These verify the categories and the supplied counit without adding a scheme-level qcqs hypothesis.

For step 2 the new statement says precisely that the comparison sends an open shifted morphism u to Rg_*u and commutes with open restriction. The existing open Ext comparison is natural in its second argument, so postcomposing the sheaf comparison with internal Hom of epsilon becomes postcomposition by epsilon[q] on Hom groups. The new node's remaining work is the evaluation computation: transpose the comparison, use the relative cup product, and evaluate; for a represented morphism u this is the image of evaluation composed with u. The pullback/direct-image counit triangular identity reduces it to Rg_*u. Restriction preserves this construction because the restricted K-injective model computes direct image, internal Hom and the section comparison; degree q is degree zero after shifting. This computation is independent of trace duality and is a real supporting lemma rather than a clause of the item.

For step 3 the pullback-restriction, tensor-restriction and direct-image-restriction statements each give exactly their displayed identifications; none presupposes global quasi-compactness or boundedness. The restricted counit is the one in the hypothesis. Use the local adjunction on E|_U[-q], not an unstated compatibility of G with shift. The exactness and shift comparison of Rg_* then give the required degree-q bijection. Quasi-coherence survives open restriction by its local definition. Affine overlaps are never assumed affine.

For step 4 the direct-image section-presheaf theorem applies to the identity morphism and arbitrary A,B, including non-quasi-coherent internal Homs. It explicitly gives natural sheafification to their cohomology sheaves. Affine opens form a neighbourhood basis by the scheme definition, so germ representatives and equalities shrink to affines and the step-3 bijections induce stalkwise bijections. Injectivity and local lift uniqueness glue by the sheaf axiom, giving cohomology sheaf isomorphisms. The definition of the derived category then inverts this quasi-isomorphism. The same direct-image theorem and the open Ext comparison give the two global degree-zero Hom groups. The computation from step 2 proves that the bijection is exactly composition with epsilon after Rf_*, not an unspecified bijection.

I tested the identity morphism with an arbitrary supplied trace (the local hypothesis forces the associated endomorphism to be invertible), empty source/target, non-quasi-compact schemes, complexes with unbounded cohomology, and non-perfect E. The argument does not require internal Hom to be quasi-coherent. The new comparison lemma works for the identity and empty morphisms and imposes no unsupported invertibility claim. All proof steps are below 2000 characters; the supporting comparison computation was separated rather than hidden in a long step.

The Mathlib searches were actually run with msearch.py and are in searches.jsonl. A second formulation was tried for the item and the new node. Derived.Adjunction.derived/derived' requires a prior adjunction; Scheme.Modules.pullbackPushforwardAdjunction and restrictAdjunction concern underived sheaves. Ext.Map is for exact functors on abelian categories, whereas Rf_* is derived from a generally nonexact functor. The cartesian closed functor results and condensed-module section formulas do not specialize in one line to the ringed-space comparison. I read the relevant Mathlib source and the local project's comparison declarations. No Mathlib leaf was claimed.

Generic tools from Picard, purity and trace units are declared in split_report.tool_uses; these are coherent-module derived-category tools unavailable in the present finiteness unit.

## Unfinished work

No part of the item's argument remains unwritten. The one supporting node intentionally remains statement-only for the next DAG level. No Lean was written or compiled.
