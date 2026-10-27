## What changed

Reconstruct the arbitrary augmented ordered-coordinate complex from the actual tensor
complex over its coefficient ring. Lift the coordinate equivalences to one-point module
sheaves, prove the cochain equations using uniqueness of algebra maps out of localizations,
and prove the augmentation equation by cancellation of the single-object coordinate
isomorphism. Apply the additive global scalar extension to this isomorphism and compose
with the tensor base-change comparison.

The two remaining mathematical calculations are stated separately in
`Sheaf.Paper.RingTensorCechCoordinates` (pure ring tensor expansion) and
`Sheaf.Paper.GlobalSectionTensorBaseChange` (base change of the actual tensor construction).
Their hypotheses and conclusions concern different parts of the original argument. Neither
contains the arbitrary input complex or its supplied coordinates. All data constructions
use the existing `ringedExtendedCech`, without choosing data from an unproved existence
statement. The target statement and its public imports are unchanged.

## Proved and sorry left

Closed the existing hole `CategoryTheory.ringFamilyGlobalExtension_ordered_iso`
(node `lem-weil-pbc-global-section-ordered-cech-tensor`) from two strictly smaller
calculations. This is a decomposition: one hole closed, two holes added, net minus one.

New holes:
- `CategoryTheory.ringTensorCech_coordinates`
  (`lem-weil-pbc-ring-tensor-cech-coordinates`).
- `CategoryTheory.ringFamilyGlobalExtension_tensor_iso`
  (`lem-weil-pbc-global-section-tensor-base-change`).

The assigned module has zero holes. All private helpers are proved. No definition has
postponed data or a postponed proof field.

## No longer needed

No existing module is withdrawn and no existing public import is removed. The original
localization-base-change dependency is still required by the tensor base-change calculation;
it is not pruned. Both original construction dependencies are retained. There is no derived
category, replacement resolution or K-flatness argument in this comparison, as required by
the assigned statement.

## Where the brief, the DAG or earlier work was wrong

The listed proof dependencies supply localization base change and the constructions but
no declared theorem for the subset expansion of the tensor complex or preservation of
that construction by this particular global scalar-extension functor. The new declarations
isolate these two calculations, while the supplied-coordinate reconstruction and augmented
composition are actual Lean proofs. The new calculations include empty lists, repeated and
zero generators, zero rings, and arbitrary sites.

The inherited blueprint ancestry lookup returns `None` because the older `created.item`
chain stops at a module name. The new records retain this inherited ancestry and identify
the precise original proof steps and Stacks source rather than inventing a blueprint node.

## New nodes

`lem-weil-pbc-ring-tensor-cech-coordinates` records the finite subset expansion over a
single ring. It has no general site, global scalar extension or arbitrary coordinate
complex. Its construction is the existing tensor construction on the one-point ring site.

`lem-weil-pbc-global-section-tensor-base-change` records the base-change comparison for
the actual tensor complexes, including the fixed augmentation. It assumes no coordinate
model and performs no identification of the tensor differential with ordered face sums.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
