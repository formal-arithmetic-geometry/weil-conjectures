## What changed

Proved `WeilConjectures.sfIntegralDirectImageShiftComparison` in
`Sheaf.Paper.SfIntegralDirectImageShiftComparison`, keeping its signature unchanged.
The sequence limit already commutes with shifts as exact scalar restriction
followed by an unbounded right-derived additive limit. Transfer this structure to
the actual reduction functor through the coefficient calculus's recorded
adjunction, using `Adjunction.leftAdjointCommShift`. Compose with exact restriction,
the right-derived tower direct image, and the right-derived inverse limit.
`Functor.commShiftIso_zero` proves the precise zero normalization.

Updated the declaration's proof description and its node's proof, proof dependencies,
and proof origin. Added the private proof import `Mathlib.CategoryTheory.Shift.Adjunction`.
Retained the exact-functor and right-derived-functor proof imports used for their shift instances.
All public imports and all other modules are unchanged. Server single-file compilation passed.
The proof preserves independent site and coefficient universes `t` and `u`.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.sfIntegralDirectImageShiftComparison`
(node `lem-sf-integral-direct-image-shift-comparison`).
No holes remain in the item module; no holes were added or split off.
This is a proof from existing recorded declarations, including the coefficient
calculus and the ambient realization, whose pre-existing proof dependencies may
still contain holes. It does not claim that those dependencies are proved.

## No longer needed

Removed these six private proof imports and their corresponding direct proof dependencies:

- `Sheaf.CategoryTheory.SystemRingedSequenceSite`
  (`lem-pur-system-ringed-sequence-site`): no reconstruction of systems as sequence-site modules.
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`
  (`lem-weil-pbc-ringed-topoi-derived-pullback`): reduction gets shifts directly from its adjunction.
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
  (`lem-pe-constant-left-module-inverse-image`): no new identification of coefficient inverse images.
- `Sheaf.Paper.SemilinearDerivedSections`
  (`lem-coef-semilinear-derived-sections`): the actual ambient realization uses the already
  specified right-derived completed-module tower direct image.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
  (`prop-pur-kinjective-resolutions-exist`): tower resolutions are already provided by
  `CoefficientRingedSequenceSite`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
  (`lem-weil-pbc-ringed-strict-tower-homotopy-limit`): the actual final functor is already
  the total right-derived limit, whose shift structure follows from the generic theorem.

Also removed the direct proof dependencies `def-weil-proetale-inverse-image`,
`def-weil-derived-direct-image`, and `def-weil-triangulated-category` from the node:
the proof composes the actual ambient realization's four functors, without
rebuilding the geometric operations or invoking abstract triangulated axioms.
These remain wherever required by statement dependencies or other modules.
Removed the six obsolete `tool_uses` approvals corresponding to the six imports
listed above, retaining the calculus and right-derived-shift approvals in their
original order. No modules are withdrawn, and no claim is made that these nodes
are globally unused.
The unit `sk-prop-sf-biduality-general` has no recorded realized statement or steps
that this shorter argument could bypass; its mathematical route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The old proof plan reconstructed more structure than shift compatibility requires.
The already recorded reduction/sequence-limit adjunction and generic shift
instances suffice for the exact functor in the statement. The original statement
is preserved, including its zero normalization and absence of boundedness conditions.
No definition, target, source-library declaration, or statement was repaired.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
