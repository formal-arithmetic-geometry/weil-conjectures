## What changed

Proved `SheafOfModules.SequenceProjection.sequenceTensorAugmentationUnit` from the
existing normalized `pushforwardLimitProjections` presentation. Its statement is factored through the definitionally equal public predicate
`augmentedDerivedLimitProperties`; its docstring and all existing public imports
are unchanged. No other existing Lean
module is changed.

Added the proved abstract theorem
`SheafOfModules.SequenceProjection.normalizedTensorAugmentation` in the new module
`Sheaf.CategoryTheory.SequenceTensorAugmentationNormalization`. It constructs the
ordinary mate, derives the constant/limit adjunction, extends the supplied
K-injective comparison to all complexes, and identifies the whole derived mate
by injectivity of the tower Hom equivalence. The total-limit equality follows
from the same normalized Hom formula, without detecting equality by projections.
The calculation holds for every complex; the requested flat-term K-flat clauses
are its specialization.

The item supplies Grothendieck K-injective resolutions and the exact ordinary
section formula. For the latter, apply the existing tensor-transpose equation at
the identity and scalar 1. Proved private conjunction helpers and the public
predicate retain the original eleven normalization clauses in exactly their
original order. Unfolding the predicate recovers the original statement.

Profiling identified repeated concrete instance comparisons in the original
assembly. Factoring the comparison conjunction and doing the mate calculations
in abstract abelian categories reduced that work. The fully proved abstract
calculation is in its own module so each file can compile separately. This is a
compilation split, not a decomposition into unproved statements. Updated the
item's DAG proof and added the matching node for the abstract calculation.

Validation: the final clean modules compile independently in 10.5 s
(normalization) and 46.4 s (item). A temporary client containing the complete
original expanded statement proves it by `exact sequenceTensorAugmentationUnit
A B α` and compiles in 20.3 s; the client was removed before delivery. Axiom
inspection of both delivered theorems and that original-statement client reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed the one original hole:
`SheafOfModules.SequenceProjection.sequenceTensorAugmentationUnit`
(`lem-sf-sequence-tensor-augmentation-unit`).

Also proved the new abstract theorem
`SheafOfModules.SequenceProjection.normalizedTensorAugmentation`
(`lem-sf-sequence-tensor-augmentation-normalization`).

Holes closed: 1. Holes added: 0. Split-off unproved statements: 0. There are zero
`sorry` tokens in either delivered Lean module. This is a proof from existing
dependencies, not a claim that all their transitive proofs are closed.

## No longer needed

Removed from the item's proof imports:
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`,
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`,
`Sheaf.SixFunctors.ResolvingDerivedAdjunction`, and
`WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.
The last remains available through the public imports of
`DerivedTowerCounitProjections` and is used by the abstract normalization module.

The following old direct proof dependencies are unnecessary for this assembly:
`def-pur-sheaf-tensor-product` (the existing tensor-transpose equation already
specifies the section), `lem-coef-restricted-tower-resolution-acyclicity` and
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition` (the normalized
comparison is already supplied by `pushforwardLimitProjections`),
`lem-coef-sequence-adjunction-cochain-transposes` (use the stronger Hom formula
already in the presentation), `lem-coef-sequence-projection-derived-adjunction`
(already included in that presentation), `lem-pur-system-ringed-sequence-site`
(use the existing strict-system Grothendieck theorem),
`lem-sfb-resolving-derived-adjunction-normalization` (Mathlib's derived-adjunction
factorization supplies the exact-constant formula), and
`prop-pur-kinjective-resolutions-exist` (use the general Grothendieck K-injective
resolution theorem).

`lem-coef-derived-tower-counit-projections` and
`lem-weil-pbc-termwise-adjunction-homotopy` are used by the new normalization node.
These are removals of direct proof requirements, not withdrawals: unchanged
parent presentations can still need the listed modules and nodes. No existing
module or declaration is withdrawn, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The plan repeats construction and normalization already present in
`pushforwardLimitProjections`. Its cochain Hom formula and comparison on
K-injective resolutions suffice. The latter extends to all complexes by
naturality and cancellation along localized resolutions. There is no need to
repeat the sequence-site construction or separately prove cochain transposes.

## New nodes

`lem-sf-sequence-tensor-augmentation-normalization`, in
`dag/nodes/sec-six-functors/lem-sf-sequence-tensor-augmentation-normalization.json`,
records the proved abstract mate calculation. It assumes normalized ordinary and
derived adjunction data, K-injective resolutions and the resolution comparison;
it constructs the augmentation and proves its unit, cochain and total-limit
identities. It does not reproduce the item's sheaf presentation or its tensor
section clause. Three kinds of Mathlib search found the derived-unit and Hom
identities used in its proof, but no theorem performing this combined argument.
The definitionally equal statement factorization is documented in
`coord/changes/sequence-tensor-augmentation-properties.md`. No target statement
or existing definition changes.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
