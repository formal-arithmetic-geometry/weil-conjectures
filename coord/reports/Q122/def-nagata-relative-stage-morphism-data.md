# Stage-1 report: def-nagata-relative-stage-morphism-data

## Files written

- `dag/nodes/sec-nagata-compactification/def-nagata-relative-stage-morphism-data.json`: definition, split using six existing definition nodes; not a Mathlib leaf. Statement retained verbatim, source updated to the current main-20261015 snapshot, blueprint.same_as searched and set to [], missing notion dependencies added, six actual search results recorded.
- `citations.json`: [] because the item is a definition with no proof steps.
- `report.md`: this report. No new nodes, no Mathlib leaves, no unit record changes, no Lean edits or compilation.

## Attachments

None. `AlgebraicGeometry.Scheme.Hom.NoetherianStageData` in `lean/WeilConjectures/AlgebraicGeometry/FinitePresentationModel.lean:100` records iX, iS, phi, compatibility w and the immersion property. It does not record the finite affine charts, finite generator-and-relation lists, affine cover of X, coordinate-ring surjections or their overlap witnesses required by the blueprint definition. The chosen `AlgebraicGeometry.Scheme.Hom.noetherianStageData` at line 182 returns that smaller structure, with extra qcqs and locally-finite-type hypotheses. Neither states the whole item, despite the matching docstring tags. I therefore did not attach or remove the blueprint's additional data.

## WANTED

None. All sources needed for this definition are present locally.

## Corrections and observations

The original statement and blueprint_update agree with main-20261015, order 387. The node still pointed at master, order 380; the source now points at the current snapshot. Its two imported dependencies cover the chosen inverse systems and comparison maps but omit the schemes, affine spectra/coordinate maps, fibre product and immersion notion. I added the existing nodes defining those notions. The blueprint_kind, blueprint_order, blueprint_uses, blueprint_update, blueprint_notes and import_flags are retained untouched.

This is a definition, not an existence theorem. No hypothesis asserting finite type of f has been added, and no claim that every f has such a datum has been made. The existence lemma remains separate. No proof was imported or hidden in a child node. The historical bypass note does not replace the full definition by its smaller formalized interface.

## Not duplicates

No new nodes are created. Whole-DAG and blueprint searches for finite-stage, finite-stage datum, stage-morphism and generator-and-relation found the item, its existence lemma and its immersion-model user. The latter two use such a datum rather than define the same record. No other blueprint node defines this entire record, so same_as is []. The existing finite-affine-gluing-presentation and morphism-descent nodes were also read: neither defines the present datum, and neither is needed as a dependency for an ordinary finite list of charts and map equalities.

## Mathlib search assessment

Every recorded search was run through the required msearch.py command and is in searches.jsonl. All four services returned results successfully; no unavailable result is recorded as absence. Two LeanFinder phrasings were tried. The first returned AffineTransitionLimit auxiliary covers and eventual equality lemmas. I read the auxiliary structure at Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean:468 and the equality lemmas at lines 635 and 690: these concern two maps from stages in one diagram and eventual equality; they do not define this record between two approximations with the required retained data. The second phrasing and LeanSearch returned IsImmersion and various ideal-sheaf or immersion properties, not the compound datum. I read Mathlib/AlgebraicGeometry/Morphisms/Immersion.lean, including IsImmersion at line 44 and its factorization characterization. The grep searches found no named stage-data structure and only the immersion component in the second search. Loogle returned zero hits. Generic scheme/immersion declarations are not a one-line specialization giving the additional stored data, so the item is split rather than marked mathlib.

## Review by Q122

I read the chapter and unit records and the current blueprint definition `literature/blueprint/main-20261015/blueprint/sec-nagata-compactification/sk-prop-nagata-sketch-fp-models/def-nagata-relative-stage-morphism-data.md`, as well as the neighbouring existence proof and unit statement. The finite-stage datum is bookkeeping preceding the unit's finite-presentation-model construction. Keeping it as a definition with no existence assertion follows that route, without replacing a unit step or changing a unit realization. No new node needs a separate source review.

I opened all six statement dependencies. `def-nagata-noetherian-inverse-system` actually supplies the cofiltered categories, finite-type stages, affine transitions and limit cones with original source schemes as vertices. `def-nagata-glued-limit-comparison` supplies the comparison to the inverse limit and records the compatible maps from the original scheme to its stages; no isomorphism theorem is needed just to form a datum. `def-pc-scheme` defines schemes, their morphisms, affine schemes and open subschemes. `def-weil-affine-spectrum` gives the contravariant ring-map/morphism correspondence for the recorded affine charts. `def-pc-fibre-product` states exactly the universal property giving the induced comparison to X_stage times S: its compatible pair is the X-stage projection and f, and the compatibility equation is part of the datum. `def-weil-closed-immersion` defines an immersion as a closed immersion followed by an open immersion and includes the affine-surjection description of a closed immersion. Thus these are definitions used for their actual stated meaning, not for an unstated descent or existence result. The item has no proof steps; C1/C4 proof-step citations and long-step checks are vacuous, and citations.json is correctly empty. There are no off-unit proof-tool uses.

For the immersion-chart interpretation I read Stacks schemes.tex, definition-immersion (Tag 01IO), and morphisms.tex, lemma-closed-immersion (Tag 01QO), using tags/tags to verify the labels. A certificate must describe a closed immersion into an open neighbourhood in the fibre product, with the source charts the full inverse images of target affine opens and with compatible overlap identifications; arbitrary surjections on unrelated source charts do not suffice. The source expressly requires charts showing an immersion and all overlap equalities; that full requirement is retained rather than replaced by a source-local surjectivity claim. Neither target opens nor X-overlaps are assumed affine without selected charts, and no finiteness of the kernel ideals on X is required.

I tested the definition on the empty scheme (empty cover and empty lists are allowed), on the identity morphism of Spec Z with constant approximations (one chart and zero presentation relations), and on an affine quotient Spec(A/J) into Spec A (the certificate uses the surjection A to A/J; J need not be finitely generated). These checks separate finite presentation data for the finite stages from a potentially infinitely generated immersion ideal on the original X. For a general f the record may be empty; the definition does not assert a witness and so does not require the finite-type hypotheses of the separate existence lemma. The displayed compatibility has codomain S_stage on both sides, and the fibre product is over S_stage, not over S or X_stage. All these clauses remain exactly the blueprint's statement.

I checked delivery-errors B through E in both occurrences: no new-node-only schema, duplicate-pair or search audit is outstanding; the dependency additions are existing notions; no proof or hidden child lemma was added; TeX has single backslashes after decoding; no target or unit statement was weakened. Only sandbox files have been written. The mathematical correction was to the missing notion dependencies, not to the statement.

## Unfinished work

None in the stage-1 definition split. The existence theorem and downstream finite-presentation models are separate items; this delivery asserts no proof of them.
