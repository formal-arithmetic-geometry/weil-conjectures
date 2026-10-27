## What changed

Replaced the hole in `AlgebraicGeometry.Etale.rawRestrictedResolution_class` by a chain-
representative reduction. For an arbitrary raw class z, compose with the specified shifted
augmentation, use the localization bijection for the shifted K-injective injective resolution, and
lift the homotopy class to a chain map c. Full faithfulness of the bounded-below inclusion and
cancellation of the augmentation recover z from c. Apply two distinct chain-level comparison
statements and use extensionality of additive group homomorphisms.

Added `Sheaf.AlgebraicGeometry.RawRestrictedResolutionCocycle`, containing the explicitly
constructed shifted resolution, shifted augmentation isomorphism, section-cocycle comparison
isomorphism, and the shift/augmentation comparison square. Added
`Sheaf.AlgebraicGeometry.ResolutionCocycleAdjunctionClass`, stating the separate cocycle-to-
derived-adjunction-class identity. Each identity is a strict part of the original argument: the
first contains no chain map, raw class, generator evaluation, higher-direct-image class or
sheafification; the second contains no raw restricted cohomology comparison. Both apply to an
arbitrary injective resolution, with no additional geometric assumptions. Their data are real
constructions from existing functors and isomorphisms, never choices from unproved existence
theorems. Updated the parent DAG proof to the actual chain-representative reduction. All existing
signatures, definitions, and public imports are preserved. Server compilation succeeded for all
three modules (the parent in 49.3 seconds); diagnostic traces were then removed for delivery.

## Proved and sorry left

Closed the original hole of `AlgebraicGeometry.Etale.rawRestrictedResolution_class` by
decomposition into two chain-level steps. The parent module has zero remaining holes. Added two
holes:

- `AlgebraicGeometry.Etale.rawRestricted_resolution_shift_square`, node
  `lem-weil-pbc-raw-restricted-resolution-cocycle`.
- `AlgebraicGeometry.Etale.resolutionCocycle_adjunction_class`, node
  `lem-weil-pbc-resolution-cocycle-adjunction-class`.

Each remaining proof is exactly `by sorry` in its own new public statement module, with source and
a complete natural-language proof. This is a decomposition (one upper hole closed, two lower holes
added), not a claim of a net hole reduction. The shifted resolution, shifted augmentation and section-cocycle comparison
isomorphism contain no holes. The restricted shifted-resolution K-injectivity helper is proved.

## No longer needed

No existing imports or modules were removed, and no module is withdrawn. The parent proof still
directly applies `lem-sbc-raw-restricted-resolution-evaluation`. It no longer directly uses `prop-
weil-pbc-derived-inverse-image-adjunction` or `lem-weil-pbc-derived-adjunction-commshift`; they
remain needed in the two new lower steps. `lem-sbc-abelian-higher-direct-image-class-
compatibility` is unnecessary for this fixed-resolution calculation: its conclusion is naturality
for a different geometric pullback, not a comparison of cocycle representatives. Its module
remains publicly available through the unchanged normalization-data module because the class
construction itself is defined there. Thus none of these modules is globally pruned. The
K-injective localization bijection remains a direct dependency of the parent.

## Where the brief, the DAG or earlier work was wrong

The old node presented the entire comparison as one proof step. Its declared resolution-evaluation
lemma only treats chain maps into a K-injective complex before undoing the shift, and its class-
compatibility lemma concerns geometric pullback. Neither states the two normalization identities
needed to combine those ingredients. The new statements isolate those identities instead of
restating the parent equality. The bounded-below complex localization functor has no registered
CommShift instance; the shifted augmentation is therefore constructed with the unbounded
localization shift comparison and the fully faithful bounded-below inclusion. No existing
mathematical statement was changed. Local irreducibility attributes keep the large comparison
constructions folded during the parent proof; their values and public attributes are unchanged. A dependency-graph traversal encountered the pre-existing
cycle through lemma-weil-pbc-derived-exchange-replacement, lem-weil-pbc-derived-exchange-termwise,
lem-weil-pbc-derived-exchange-unbounded-transport, and lem-weil-pbc-derived-exchange-bounded-
comparison; this delivery changes none of those nodes and introduces no edge back to the parent or
either new node. The blueprint ancestor helper cannot follow the parent created.item because it is
a Lean module name; the new nodes retain the valid explicit blueprint ancestor already recorded in
the parent.

Checked small cases on the definitions: at q=0 the shift comparisons give the unshifted
augmentation and ordinary generator evaluation. For a zero chain map the cocycle-class identity
has zero on both sides by additivity; the comparison square also sends zero to zero. For an empty
pullback the restricted sections complex has zero groups and the unit-evaluated generator is zero;
the same identities apply without a nonemptiness hypothesis. No positivity, properness,
noetherianity, torsion or affine hypothesis has been inserted.

## New nodes

`lem-weil-pbc-raw-restricted-resolution-cocycle` isolates the comparison between the shifted
augmentation and the prescribed resolution computations, before any raw-class evaluation or
sheafification. The parent combines this square with the already-proved
rawRestricted_resolution_evaluation theorem by functoriality. The node records all five
declarations in its new module, including the proved K-injectivity of the restricted shifted
resolution.

`lem-weil-pbc-resolution-cocycle-adjunction-class` identifies the image of this section cocycle
through the prescribed sheafification/counit/augmentation maps with the derived adjunction class.
Its proof follows the termwise adjunct and evaluates its generator.

Both are below the existing proper-base-change unit route. Searches used LeanFinder, Loogle,
LeanSearch and grep through msearch.py, plus local searches of both source roots and the DAG. The
blueprint search for resolution cocycles found no match; the higher-direct-image-presheaf
blueprint statements do not prescribe either new chain-level comparison. No change record is
needed: existing public interfaces and all existing definition bodies are unchanged.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
