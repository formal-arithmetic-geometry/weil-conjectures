## What changed

Replaced the proof of `AlgebraicGeometry.Etale.compactSupportFiniteTorsion` by the existing
exchange-invertibility instance and a common-refinement cancellation argument. The original
theorem signature is unchanged. Proved private adjunction, Cartesian-comparison and
composition helpers in the item module. The compositor calculation uses the existing concrete
`rightDerivedFunctorPlusCompIso'_lowerStarComp_assoc`, with a proved API equation for the
refinement-map construction. Added the proof-only imports of
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison` and
`Sheaf.AlgebraicGeometry.ProperOpenIdentificationNormalization`.

The public definition `compactSupportProperOpenRefinementMap` keeps its signature and now
uses the concrete derived direct-image compositor directly. The existing proved
`derivedPlusFormalism_pfComp'_inv` identifies this with its previous formalism compositor,
so it constructs the same map. This repairs costly kernel conversion in the definition.
The construction change, proof-local controls and consumer check are recorded in
`coord/changes/B2-compact-support-refinement-interface.md`.

## Proved and sorry left

Original holes: 1, `AlgebraicGeometry.Etale.compactSupportFiniteTorsion`.
Its combining proof is complete; there are no holes in the item module.

New holes: 1, `AlgebraicGeometry.Etale.properOpenIdentification_unit`, node
`lem-weil-pbc-proper-open-identification-unit`, in the new module
`Sheaf.AlgebraicGeometry.ProperOpenIdentificationNormalization`.
It still needs the clopen-section component-restriction characterization transported through
open base change and the mate counit equation. In scratch work, the derived-open-unit formula
and the generic section-cancellation identity were proved and compiled; the geometric
transport through the exact specified theta remains unfinished. Its docstring gives the three
steps and the normalizations to check. It is a restriction equation, with no compactification or arbitrary
refinement comparison conclusion; the adjunction calculation, compositor calculation and
common-refinement cancellation are actual proofs in the item module.

This is one decomposition, not a net proof: one original hole closed, one lower hole added,
net zero. Both delivery modules compile without warnings. The full item compiled in
9.3 seconds; a separate consumer check proving equality with the original definition
formula compiled in 6.5 seconds. The delivery dry run passed its preflight.

Existing imported sorries (including `properOpenComparison_comp` and
`isIso_properOpenComparison`) are unchanged and are the intended next proof dependencies.

## No longer needed

Removed proof imports:

- `WeilConjectures.Compactification.BaseChange`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `Mathlib.CategoryTheory.Adjunction.Mates`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`
- `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`
- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`
- `WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical`
- `Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence`

The following planned nodes are no longer direct proof dependencies of this item:

- `lem-weil-pbc-extension-by-zero-exact`
- `def-cbc-compact-support-square`
- `thm-weil-pbc-bounded-below`
- `lem-weil-pbc-exchange-forget-coefficients`
- `lem-cbc-proper-open-interchange-coherence`
- `lem-weil-pbc-mate-pasting`
- `lem-cbc-etale-derived-direct-image-coherence`
- `lem-cbc-cofiltered-span-comparison`
- `lem-cbc-compactifiable-compatible-tower`
- `lem-cbc-extension-zero-composition`
- `lem-cbc-tower-composition-refinement`

The exchange and its coherence already have the upstream API recorded on this mixed node.
The source library already proves concrete direct-image compositor coherence and the canonical
common-refinement ratio, so a second normalized direct-image pseudofunctor, a cofiltered-span
construction, a tower construction and a coefficient-forgetting proof are unnecessary here.
These removals concern this item's direct work; they do not claim the modules are unreachable
from every target or from all remaining imported dependencies. No library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The plan omits the explicit equation normalizing the specified geometric restriction theta
against the derived adjunction counit. An isomorphism alone does not identify its transpose
with the formalism comparison. The new node supplies exactly this missing restriction step.
The proposed dense common refinement can be taken as `inf c c`; the existing
`isPullback_of_inf` API makes its composite with every refinement Cartesian over the open.
The existing Noetherian comparison theorem cannot be applied because this item has no
Noetherian hypothesis.

The compile-time problem occurs in conversion between the formalism compositor and the
concrete chosen-resolution functor interfaces. The stored construction now uses the concrete
compositor; the original signature and intended map are preserved by the existing normalized
compositor theorem. Targets depending on this definition require semantic re-review.
No claim about a finished library proof follows from the decomposition.

## New nodes

`lem-weil-pbc-proper-open-identification-unit` states the canonical restriction equation for
the already specified theta, over arbitrary schemes and finite commutative coefficients.
Its proof uses the existing clopen-section characterization, the termwise/derived
open-extension unit equation, and mate/compositor identities. Checked the empty open, zero
ring, identity proper map and possible extra boundary components; no density or Cartesian
condition is needed. Searches in Mathlib and the local library found no matching theorem.
The equation is strictly an internal part of the refinement normalization argument.

Change record: `coord/changes/B2-compact-support-refinement-interface.md`.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
