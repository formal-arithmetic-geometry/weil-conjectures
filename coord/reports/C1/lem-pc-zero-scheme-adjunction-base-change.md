Files written:

- `dag/nodes/sec-picard-framework/lem-pc-zero-scheme-adjunction-base-change.json`: statement node, split using an existing stronger DAG theorem; no Mathlib leaf.
- `citations.json`: verbatim statement quotes for the one proof step.

Attachments:

- None. `AlgebraicGeometry.nonempty_arrowIso_pullback_directImageCounit` has a `sorry` in `WeilConjectures/AlgebraicGeometry/Picard/ZeroScheme.lean:165-175`.

WANTED: none.

The source declaration's statement matches the item, but its proof is sorried. I found the existing node `lem-pc-arrow-iso-pullback-counit`, whose statement is strictly more general (arbitrary field and geometrically integral curve) and whose proof already establishes the Arrow isomorphism. The current item's separably closed hypothesis supplies geometric integrality through `prop-pc-xk-integral`; the remaining hypotheses and the notation for the base-change map and pulled-back Picard object match directly. Thus the item needs no new node and is proved by specialization.

## Not duplicates

`lem-pc-zero-scheme-adjunction-base-change` vs `lem-pc-arrow-iso-pullback-counit`: the existing node has weaker field/curve hypotheses (arbitrary field and geometrically integral curve), while this item fixes a separably closed field and uses the corresponding specialized notation; it is the same conclusion under a strict specialization.

## Review by C1

I read the item source and docstring in `WeilConjectures/AlgebraicGeometry/Picard/ZeroScheme.lean`, including lines 156-175, and checked that the project declaration is not attachable because its body is `sorry`. I read the full statements and proof of `lem-pc-arrow-iso-pullback-counit`; it explicitly gives the pullback of the direct-image counit as an Arrow isomorphism for a morphism `i : T' -> T`, exactly the fact needed here. I also read `prop-pc-xk-integral`, whose second clause says that a smooth projective curve over a separably closed field is geometrically integral, verifying the only additional hypothesis required by the stronger existing node. The sole proof step cites both statements, and each citation quote in `citations.json` is copied verbatim from its node. I checked the edge case of a separably closed field with `T'=T` and `i=𝟙`, where the result reduces to the identity counit comparison. No new node was warranted: creating one would duplicate the existing stronger theorem.

## Second reading by C1

- Source item: read `ZeroScheme.lean`, theorem `nonempty_arrowIso_pullback_directImageCounit` (lines 143-175), including the section-wide hypotheses; the repaired statement now includes the required injective-resolution hypothesis and matches the theorem's counit/base-change assertion.
- Step 1: checked against `lem-pc-arrow-iso-pullback-counit` and `prop-pc-xk-integral`; the former supplies the Arrow isomorphism under geometric integrality and injective resolutions, while the latter supplies geometric integrality from the separably closed smooth projective curve with rational point. Verdict: valid specialization after the hypothesis repair; no unquoted non-elementary fact remains.
- Item node: checked self-containment and definition references for separably closed field, smooth projective curve, rational point, injective resolutions, Picard subfunctor, invertibility in degree zero, and base change. Verdict: statement-only form is appropriate for the item and all cited notions are defined.
- Edge cases: checked `T'=T` with `i=𝟙`, a field-valued base, and the empty base scheme; no additional conclusion or hypothesis is introduced by these cases.
- Existing-node search: searched the DAG for the item and counit/base-change keywords; `lem-pc-arrow-iso-pullback-counit` is the existing stronger theorem, so no helper node is needed. The worker's Mathlib searches record only generic infrastructure and no exact match.
- Metadata: corrected `created.item` to this delivered item; the prior value incorrectly named `lem-pc-zero-scheme-recd`.

Changes made: added the source-required injective-resolution hypothesis and `[def-sp-injective-resolutions]` dependency, corrected ownership metadata, and recorded the second-reading audit.
