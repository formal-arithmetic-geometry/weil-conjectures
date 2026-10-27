## What changed

Replaced the hole in `AlgebraicGeometry.square_injectiveRoof_action` by an explicit
coefficient-roof calculation and a categorical naturality/cancellation proof. Its
statement, public imports and all existing shared definitions remain unchanged.
The degree-zero augmentation equation is extended to integer cochains, localized,
and combined with naturality of the right-derived unit. No preservation of
injectives by a direct image is assumed. The standard right-derived functor and
its unit are locally irreducible in the final combination; this prevents expensive
unfolding and brings the item within the 60-second compile limit. No shared
definition or reducibility setting is changed.

Added `DirectImageSectionUnit`, constructing the natural inverse-open cochain unit
followed by local Leray and the unique unit-preserving comparison with the standard
derived direct image. Its comparison with the published pointwise Leray model and
its evaluation/naturality API are proved. Added `InjectiveSectionUnitComparison`
to prove that the raw injective comparison preserves this unit. The only unresolved
step is isolated in `SquareSectionUnitCancellation`.

Validation: the final remote `lcompile.py --all` run compiled all four files
cleanly in 50.7, 26.4, 2.2 and 51.0 seconds respectively, each below 60 seconds.
The original theorem signature and original public-import list were also checked
to be byte-identical to the shared source.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.square_injectiveRoof_action` by a
complete reduction. The private coefficient-augmentation, coefficient-derived-roof,
roof-action algebra and section-quasi-isomorphism calculations are proved.
`AlgebraicGeometry.injectiveSectionUnit_comparison` and every declaration in
`DirectImageSectionUnit` have no holes.

Added exactly one hole:
`AlgebraicGeometry.squareSectionUnit_cancellation`, node
`lem-weil-pbc-square-section-unit-cancellation`. This is the target-representative
unit cancellation in the commuting square. It has no source coefficient sheaf,
coefficient morphism, replacement complex, numerator or denominator. It is a strict
part of the original argument; the Lean combination with the arbitrary coefficient
roof and denominator cancellation is written and checked separately.

Thus one original hole is replaced by one strictly smaller hole: this delivery is
a decomposition, with zero net reduction in the number of holes. The item module
has zero holes and the delivery has one. The new statements were checked on zero
complexes/resolutions, degree zero, empty opens and identity squares; no additional
hypothesis is needed in these cases.

## No longer needed

No original import was removed and no module is withdrawn. There is no claim of
pruning a module from the targets' closure. The square-mate and normalized-square
unit lemmas remain needed by the new cancellation node, rather than being direct
steps of the coefficient-roof calculation. The main proof uses the local-model
constructions, not the theorem `derivedAdjunction_topEdge`; the original statement
dependency and the unit route are preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically consistent. Its last two steps bundled the
coefficient-roof calculation with the independent normalization of local sections.
The new proof separates those steps and supplies the augmented cochain equality,
the localized coefficient roof, the naturality combination and the source endpoint
comparison in Lean. The normalized square calculation is still explicitly open.

The comparison between the two derived direct images is a genuinely natural
isomorphism: uniqueness of the universal pairs proves this, and its components
agree with the previously defined pointwise model comparisons. No new arbitrary
witness is selected from an unresolved existence theorem. All chosen data in the
new module are uniquely determined isomorphisms from proved universal properties.

## New nodes

`def-weil-pbc-direct-image-section-unit` records the constructed section unit and
its proved universal-comparison, model and naturality API.

`lem-weil-pbc-injective-section-unit-comparison` records the proved one-resolution
endpoint normalization. Its proof is naturality of the comparison along the
augmentation, followed by inverse identities.

`lem-weil-pbc-square-section-unit-cancellation` records the one remaining normalized
square calculation on its target injective representative. Its source, complete
proof in words, and dependencies on the existing mate, normalized-unit and local
Leray results are recorded in both its docstring and its node.

The static interface advisory sees the local attribute and `omit` commands in the
item. These commands are explicitly local or apply only to private helpers; they
change no exported attribute, instance, notation or signature. LeanSearch was unavailable for both natural-language queries; this is recorded as
unavailable, with LeanFinder, Loogle and source grep retained. No change record is
needed: no other existing module, existing definition, existing statement or node
of another module is changed. Temporary proof probes are excluded.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
