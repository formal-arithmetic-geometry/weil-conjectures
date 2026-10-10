# Stage 1 report

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-projection-locality.json`: split item with two proof steps; no Mathlib match.
- `citations.json`: verbatim citation for the non-elementary proof step.

## Attachments

None. I searched the project Lean source for the item id, its projection-formula terminology, and blueprint tags; no sorry-free declaration states this locality result.

## WANTED

None.

## Review by G1

I read the imported item and its parent blueprint proof in `lem-pc-projection-formula`, then checked the canonical map definition in Stacks `cohomology.tex`, Equation 20.54.2.1, and the locality assertion in `perfect.tex`, Lemma 36.22.1 (Tag 08EU). The first step is elementary: restriction of the canonical projection map is the canonical map for the inverse-image morphism, by the functorial definitions of restriction, derived pullback, tensor, and direct image. The second step spells out the locality argument through cohomology sheaves: restriction is exact and ordinary sheaf-module isomorphisms are local on an open cover, matching Mathlib's `AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app`.

I searched the whole DAG and blueprint before deciding that a child node would duplicate the item's own locality clause; the preflight's D1 check confirmed this, so the argument remains in the item's steps. I ran LeanFinder, Loogle, grep, and LeanSearch searches for the item; LeanSearch was unavailable and is recorded as such. I checked the identity cover and the one-open cover cases, where the equivalence reduces respectively to the original isomorphism assertion and its restriction. No Lean declaration tagged with this item exists, and no unrelated files were changed.

## What was wrong

The imported item had no proof steps. I supplied the missing restriction-identification step and wrote the cohomology-sheaf locality argument directly, avoiding a child node that would merely restate the item.

## What could not be finished

No child nodes remain; the derived-category/sheaf descent argument is recorded as the item's second proof step for later formalization.

## Second reading by G1

- Item statement: checked against the projection-formula map in `cohomology.tex` (Equation 20.54.2.1) and the locality reduction in `perfect.tex`, Lemma 36.22.1 (Tag 08EU); the quasi-compact/quasi-separated hypotheses, derived categories, open cover, restricted morphism, and iff conclusion agree hypothesis by hypothesis.
- Step 1: checked that restriction of the canonical map is the canonical map for `f^{-1}(U_i) -> U_i`, including the derived pullback, derived tensor, and direct-image restriction identifications; the identity-cover and one-open-cover cases reduce to the original map and its restriction. Verdict: correct and elementary at the stated categorical-definition level.
- Step 2: checked against Tag 08EU that isomorphisms in the derived category are detected on cohomology sheaves, restriction to an open is exact, and sheaf isomorphisms are local on an open cover; the zero object and empty/identity-cover cases behave as claimed. Verdict: correct; no separate child node is needed because this is the locality argument for the item itself.
- New nodes: none. The whole-DAG and blueprint searches found no smaller existing node that states the item's locality clause, and creating one would restate the item (D1). Thus B1-B7 are vacuous for new nodes.
- Mathlib searches: the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch queries were checked against `searches.jsonl`; they found only generic locality/functor declarations, not this derived projection-formula theorem.
- Changes made: none to the node or citations; this second-reading section records the source, dependency, small-case, duplicate, and search checks. The dry run passed `deliver.py` preflight.
