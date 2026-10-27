## What changed

The existing theorem `WeilConjectures.OpenTensorQuotient.openQuotientNormalizedCochains`
keeps its full signature and public imports. Its proof now constructs both strict
augmentations from the scalar-adjunction unit and the normalized balancing isomorphism.
Naturality proves their square; functoriality proves the localized square; homogeneous
pure-tensor extensionality identifies the first Roos coordinates.

The new coefficient-comparison module proves balancing existence from
`normalizedIntegralTensorTower`. It constructs the strict comparison by conjugating
the fixed integral comparison through balancing and scalar reduction, then lifts its
components through fully faithful scalar restriction. This proves finite coefficient
linearity without importing the larger generic coefficient-interchange theorem.

The new scalar compatibility module constructs the scalar-unit tower and proves its
section formula and naturality. Its remaining theorem isolates extension-by-zero
compatibility of scalar restriction, including the fixed component normalization and
scalar-unit equation. This is a strict part of the old argument, with no tensor square,
balancing, tensor-completion presentation, or Roos assertion in its conclusion.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.OpenTensorQuotient.openQuotientNormalizedCochains` (one original hole).
The item module has zero remaining holes.

Added one hole:
`WeilConjectures.OpenTensorQuotient.openQuotientScalarUnitCompatibility`, node
`lem-sf-open-quotient-scalar-unit-compatibility`. It has an explicit source and complete
proof in words. Thus this is a decomposition from one hole to one strictly smaller
hole, with net zero holes closed, rather than a complete proof free of dependencies.

The delivered coefficient theorem
`WeilConjectures.OpenTensorQuotient.openQuotientCoefficientComparisons`, balancing
existence, scalar-unit construction and naturality, and all assembly helpers are
proved without new holes. Existing theorem dependencies are used as stated.

## No longer needed

The item's proof-only `import all Sheaf.Paper.ProEtaleCanonicalTensorPullback` is
replaced by `import Sheaf.SixFunctors.OpenTensorQuotientRoosNormalization`; the new
module owns the proved extensionality calculation.

No existing public import or module is removed. No source-library declaration changes.
The direct proof no longer needs these old planned dependencies:

- `lem-pur-cochain-pullback-tensor-coherence`: use the existing normalized strict tensor
  tower directly for balancing.
- `lem-sf-open-total-tensor-coefficient-interchange`: construct gamma by conjugation and
  lift it through fully faithful scalar restriction.
- `lem-sf-open-tensor-scalar-unit-augmentation`: construct the augmentations explicitly
  and prove the square by naturality.
- `lem-sf-cbc-slice-tensor-generator-coherence`: no longer a direct dependency of the
  item; the smaller scalar compatibility step retains its summand argument.
- `lem-fix-constructible-tensor-completion`: no longer a direct dependency; the existing
  tensor-completion model existence theorem supplies the normalized presentations.

These are changes to this node's direct proof route. They do not claim that the modules
are globally unused, and none is withdrawn. The blueprint unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

The old plan bundled scalar transport, balancing, coefficient interchange and the
augmentation square. Once scalar transport preserves the actual scalar units, the
augmentation square follows formally by naturality. The finite coefficient comparison
also needs no separate tensor-interchange result: local surjectivity of the completed
projection makes scalar restriction fully faithful, so it lifts the strict comparison.
No existing statement has been weakened or disputed.

The quarantined item source was restored by synchronization before editing. Its Lean
attachment and mathematical statement are retained.

## New nodes

`lem-sf-open-quotient-scalar-unit-compatibility` states exactly the remaining strict
scalar comparison and unit compatibility. Its source is Stacks 03DI, 03EK, 0E8I and
0941. The empty and identity opens, zero complexes, all quotient levels, and arbitrary
cochain degrees are included.

`lem-sf-open-quotient-coefficient-comparisons` records the proved normalized balancing
existence and the finite coefficient lift. It uses the normalized integral tensor tower
and local surjectivity of the completed projection. No change record is needed: only
the assigned module, new modules, and their own node records change.

`lem-sf-open-quotient-roos-normalization` records the proved pure-section uniqueness
of the first Roos coordinate. Profiling found repeated checking in the assembled
module (63 seconds); after local folding it remained over the limit (64 seconds).
This already proved helper therefore moves to its own module. It adds no hole.
The main module's proof-only import of ProEtaleCanonicalTensorPullback is replaced
by the new normalization module; that module uses the tensor extensionality API.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
