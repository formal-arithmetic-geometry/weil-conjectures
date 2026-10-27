## What changed

Replaced the hole in `sfDirectImageTransition_presentation` by categorical pasting and cancellation from two independent steps: identification of the normalized input quotient, and compatibility of the normalized direct-image restriction squares. The private generic lemma `presentationOfPasting` proves the assembly. The assigned theorem's statement and original public imports are unchanged.

Added `Sheaf.Paper.SfDirectImageInputTransitionAdjacent`, proving the successive-index specialization of the existing compact-support input compatibility. Added two statement modules, `Sheaf.Paper.SfNormalizedInputTransition` and `Sheaf.Paper.SfDirectImageRestrictionPasting`, for the remaining coefficient-only and comparison-only calculations.

## Proved and sorry left

Closed the original hole `sfDirectImageTransition_presentation` by decomposition. The existing `sfFiniteDirectImage_presentation` stays proved. Proved the new `sfDirectImageInputTransition_adjacent` from `compactSupportInput_completed_tower`.

Added two holes: `sfNormalizedInputTransition` (node `lem-sf-normalized-input-transition`) and `sfDirectImageRestriction_pasting` (node `lem-sf-direct-image-restriction-pasting`). This is a decomposition of one hole into two strictly separate steps, not a net hole-count improvement. The first has no direct image or scheme map; the second has no completed input K, scalar extension, or reduction map. Their combination is the checked categorical proof in the assigned module.

## No longer needed

No original public imports or library modules are withdrawn. The assigned theorem's direct proof dependencies are now the two new steps. The original coefficient and normalized-direct-image dependencies remain needed through those steps; none is claimed pruned. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The input compatibility already stated in the library uses the quotient-based compact-support reduction and its compositor. The target uses the normalized `CompactSupportProperImageTower.reductionMap` and `compactSupportSystemRestrictionComp`. Identifying these specified presentations is a separate coefficient-only obligation; it must not be treated as definitional equality. The direct-image pasting obligation is independent of that quotient calculation.

## New nodes

`lem-sf-direct-image-input-transition-adjacent` records the proved successor specialization of the existing input-tower compatibility.

`lem-sf-normalized-input-transition` isolates the K-flat calculation comparing the normalized quotient transition with the canonical completed input transition.

`lem-sf-direct-image-restriction-pasting` isolates the resolution-normalized compatibility of the three direct-image restriction squares. There are no interface changes to existing modules and no change records are required.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
