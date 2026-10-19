# Stage-1 report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-oriented-nearby-smooth-source-pullback.json` — statement, split proof, blueprint provenance, and review metadata; status `split`.
- `dag/nodes/sec-trace-formula/lem-trf-smooth-source-constructible-local-acyclicity.json` — statement-only intermediate lemma, status `unsplit`, Mathlib searches found no match.
- `citations.json` — verbatim citations for every node used by every proof step.

## Attachments

None. I searched the slopmaster2 source by the item id, nearby-cycle and smooth-source terminology; no sorry-free declaration states this item.

## WANTED

- `literature/orgogozo-modifications-cycles-proches.pdf`, Section 9.3, printed p. 22, for the paper's smooth-source calculation. The local proof route is recorded against the available Stacks local-acyclicity and smooth-base-change text and the existing oriented-product interfaces.

## Not duplicates

- `lem-trf-smooth-source-constructible-local-acyclicity` vs `lem-trf-nearby-smooth-source-exchange`: the existing node treats only finite constant coefficients and compares sliced stalk cones on an open smooth locus; the new node treats arbitrary bounded constructible complexes and compares strict-local vanishing-fibre derived sections.
- `lem-trf-smooth-source-constructible-local-acyclicity` vs `lem-trf-nearby-cycle-finiteness-exchange`: the existing node is a trait-specific nearby-cycle finiteness/exchange theorem (with additional proper and finite-Tor material); the new node is a general Noetherian-base local smooth-acyclicity statement for constructible complexes.
- `lem-trf-smooth-source-constructible-local-acyclicity` vs `lem-weil-pbc-smooth-local-acyclicity`: the existing node proves universal local acyclicity only for constant cyclic torsion sheaves; the new node extends the comparison to pullbacks of arbitrary bounded constructible complexes and records the strict-local derived-section map and base-change naturality.
- `lem-trf-smooth-source-constructible-local-acyclicity` vs `lem-weil-pbc-locally-constant-torsion-local-acyclicity`: the existing node covers locally constant torsion sheaves; the new node includes finite-stratification, extension-by-zero, and truncation devissage to arbitrary bounded constructible complexes.
- `lem-trf-smooth-source-constructible-local-acyclicity` vs `def-weil-pbc-etale-shriek-base-change-map`: the existing node is a definition of an étale shriek base-change map; the new node asserts an isomorphism on strict-local derived sections for smooth pullback of constructible complexes.
- `lem-trf-smooth-source-constructible-local-acyclicity` vs `lem-weil-pbc-affine-free-etale-module-eventual-hom-lift`: the existing node concerns eventual Hom lifts for affine free étale modules; the new node concerns universal local acyclicity and strict-local cohomology under a smooth morphism.
- `lem-trf-smooth-source-constructible-local-acyclicity` vs `lem-weil-pbc-etale-shriek-base-change-modules`: the existing node proves a module-level étale shriek base-change construction; the new node proves smooth-source local acyclicity for arbitrary bounded constructible derived complexes.
- `lem-trf-smooth-source-constructible-local-acyclicity` vs `lem-weil-pbc-inverse-image-free-etale-module`: the existing node defines or identifies inverse images of free étale modules; the new node compares derived sections after smooth pullback.
- `lem-trf-smooth-source-constructible-local-acyclicity` vs `lem-weil-pbc-modulecat-upperstar-free-yoneda`: the existing node is a Yoneda statement for free module objects; the new node is a geometric local-acyclicity comparison for constructible torsion complexes.
- `lem-trf-smooth-source-constructible-local-acyclicity` vs `lem-weil-pbc-underived-exchange-module-linear`: the existing node gives an underived module-linear exchange map; the new node gives a derived strict-local cohomology isomorphism for smooth source pullback.
- `lem-trf-smooth-source-constructible-local-acyclicity` vs `sbc-prop-extension-by-zero-and-arbitrary-base-change`: the existing node treats extension-by-zero and arbitrary base-change for an open immersion; the new node treats smooth pullback and local acyclicity for arbitrary bounded constructible complexes.
- `lem-trf-smooth-source-constructible-local-acyclicity` vs `lem-asd-etale-compact-support-normalization`: the existing node normalizes étale compact-support constructions; the new node compares ordinary strict-local derived sections along a smooth morphism.
- `lem-trf-smooth-source-constructible-local-acyclicity` vs `lem-asd-open-projection-exchange`: the existing node concerns exchange for an open projection in compact-support formalism; the new node concerns smooth-source local acyclicity and its base-change naturality.
- `lem-trf-smooth-source-constructible-local-acyclicity` vs `lem-cbc-base-change-mate-stalk`: the existing node identifies a base-change mate on stalks; the new node supplies the smooth local-acyclicity isomorphism whose stalk comparison is used here.
- `lem-trf-smooth-source-constructible-local-acyclicity` vs `lem-cbc-derived-extension-zero-base-change-open-pasting`: the existing node pastes derived extension-by-zero maps for open immersions; the new node is a smooth pullback comparison for strict-local fibres.
- `lem-trf-smooth-source-constructible-local-acyclicity` vs `lem-cbc-derived-extension-zero-base-change-underived-compatibility`: the existing node checks compatibility of extension-by-zero base change with an underived map; the new node asserts universal local acyclicity for smooth source pullback.

## What was checked and corrected

The imported item had no proof steps. I retained its hypotheses and conclusion: Noetherian base, finite presentation for both maps, smooth source map, finite coefficient ring with an annihilator invertible on the base, arbitrary bounded constructible input, an object-level comparison on the vanishing topos, and compatibility after Cartesian base change. I did not weaken the conclusion to a statement about stalk cones.

The item’s proof now follows five steps. First, the oriented-product universal property constructs the induced map and identifies the comparison as the counit mate. Second, the existing oriented point-cohomology and strict-local-description statements identify each point pullback with the canonical strict-local vanishing-fibre map. Third, the new intermediate node supplies the smooth local-acyclicity isomorphism for arbitrary bounded constructible complexes; its intended source route is Stacks Tags 0GJQ and 0GJR, extension-by-zero base change (03S6), finite-stratification devissage, and truncation. Fourth, joint conservativity of oriented-product points detects the global isomorphism. Fifth, the same local argument after base change and the mate-pasting identities give compatibility of the ordinary comparisons.

I read the complete statements of every cited node, including the hypotheses on coefficient annihilators, finite presentation, strict localizations, bounded constructibility, and point conservativity. I checked the small cases $h=1_X$, $L=0$, empty source, and an identity base change; all maps reduce to the identity or a zero comparison as expected. The new node was searched in the whole DAG and blueprint before creation. Its four Mathlib searches were run and recorded; they found only generic derived-category or smooth-morphism declarations, with no nearby-cycle or local-acyclicity theorem.

## Review by Q33

I read the item source record, the `sk-i-curve-zero` unit and `sec-trace-formula` chapter, the oriented-nearby-cycle definition, oriented-product universal property, oriented point-cohomology formula, strict-local description, point-conservativity theorem, the related constant-coefficient smooth-source exchange, the trait finiteness/exchange node, and the smooth-base-change/local-acyclicity nodes used to formulate the new intermediate lemma. For each proof step I checked that every cited statement supplies the exact operation used: the universal property supplies the induced vanishing-topos map; point cohomology and strict-local description supply the two derived-section identifications and comparison map; the new lemma supplies the local isomorphism under exactly the stated smoothness, Noetherian, torsion, and constructibility hypotheses; point conservativity supplies detection; and mate-pasting supplies base-change functoriality. I verified the strict-local fibre maps are formed after base change of $h$, that the coefficient annihilator stays invertible, and that bounded constructibility is preserved under pullback. I corrected the imported empty proof by making these dependencies and the object-level conclusion explicit, and I added the missing statement-only local lemma rather than hiding its devissage in a long proof step.

## What could not be finished

No Lean code or compilation was attempted, as required for stage 1. The external Orgogozo PDF is unavailable in the local literature and is recorded under `WANTED`; the split therefore cites the available Stacks and project interfaces for its natural-language proof route.
