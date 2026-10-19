## Files written

- `dag/nodes/sec-six-functors/lem-coef-dg-semi-free-cofibrant.json`: item split into five proof steps; no new nodes.
- `citations.json`: verbatim statement excerpts for every cited step dependency.

## Attachments

None. The read-only slopmaster2 source contains no declaration tagged `(blueprint: lem-coef-dg-semi-free-cofibrant)` and no declaration stating this theorem.

## WANTED

- WANTED: Toën, *The homotopy theory of dg-categories and derived Morita theory*, §3 (projective enriched diagram model), for the model-structure route.
- WANTED: Drinfeld, *DG quotients of DG categories*, §§13.3 and 14.8, for the explicit semi-free module cell attachment and opposite-category convention.

## Not duplicates

- `lem-coef-dg-semi-free-cofibrant` vs `lem-coef-dg-semi-free-homotopically-projective`: the existing node proves homotopical projectivity via nullhomotopies, while this item proves projective model cofibrancy and the explicit sphere-to-disk cell presentation.
- `lem-coef-dg-module-semi-free-replacement` vs `lem-coef-dg-semi-free-cofibrant`: the existing node gives existence of a semi-free replacement; this item proves that every such semi-free object is cofibrant and identifies its cell filtration.

## Review by NE

I checked the item against its source field and the paragraph-2 route in `prop-coef-integral-exceptional-adjoint`: the statement's two variances, projective model, generating sphere-to-disk maps, and graded-split representable filtration are all retained. I read the complete statements of `lem-coef-dg-module-semi-free-replacement`, `lem-coef-enriched-projective-diagram-model`, and `lem-coef-small-object-cell-factorization`. Step 1 uses only the former's filtration definition and the latter's strict enriched diagram model under the opposite-category convention. Step 2 takes the latter's explicit free generating maps and its characterization of objectwise trivial fibrations. Step 3 uses the former's split representable quotients and the latter's free representable maps; I checked that the differential of each lifted quotient generator is a cycle and that the pushout universal map and its inverse agree on old elements and on every generator multiple. Step 4 uses exactly the small-object node's definition of an I-cell map and the projective node's left-lifting characterization. Step 5 uses the projective node's definition of cofibrant object. I tested the empty coproduct, zero filtration, a one-cell filtration, finite filtrations, and passage between covariant modules and right modules over the opposite dg category. The item had no prior proof; I added only the explicit cell argument and the missing small-object dependency. No statement was weakened or given extra hypotheses, and no duplicate auxiliary node was introduced.

The explicit pushout calculation follows Drinfeld §§13.3 and 14.8, which are not archived locally; the report records them as WANTED and the proof origin is agent-written. Mathlib searches were rerun for leanfinder, Loogle, grep, and LeanSearch; they found only generic cofibrant replacement or K-projective declarations and no semi-free dg-module result.

## What was wrong or incomplete

The imported node had an empty proof and omitted the generic small-object dependency needed to justify the relative-cell conclusion. The source itself does not provide an archived local proof, so the cell attachment is written out directly.

## What remains

Nothing remains for this split.
