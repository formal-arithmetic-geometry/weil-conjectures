## What changed

Replaced the sole `sorry` of
`AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction.compactSupportRestrictionCocycle`
by a complete proof from three strictly smaller factor statements. The original theorem's
signature and the five public imports are unchanged. No existing public definition or
statement was changed, and no other group's module was adapted.

The proved private helpers identify each component of `sequenceMap`, prove its composition
and identity laws using the constant-sheaf functor, and construct
`restrictionIdentifications` using the existing system scalar restriction API. Its section
normalizations are proved by reflexivity; there is no postponed data construction.

The main proof constructs `Comparison` from the open and proper factors, expands its specified
pasting isomorphism, and proves the compact-support composition equation using the two factor
cocycles and naturality of the proper comparison. The unit equation follows from the two
factor unit equations and functoriality. Finite compatibility is supplied by the third factor
statement. These are equations of whole derived systems, without evaluation faithfulness.

Added three proof imports, one new statement module and node per factor, and updated the
parent node's proof, proof dependencies, proof origin and obsolete direct tool uses.

## Proved and sorry left

Closed the original one hole, by name:
`AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction.compactSupportRestrictionCocycle`
(node `lem-weil-system-compact-support-restriction-cocycle`). Its module contains zero holes.
The private component, composition and identity lemmas and restriction-identification
construction are fully proved.

Added exactly three named theorem holes, each in its own new module:

- `AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction.systemOpenRestrictionCoherence`
  (`Sheaf.Paper.SystemOpenRestrictionCoherence`,
  node `lem-sp-system-open-restriction-coherence`). This is the open-extension factor alone,
  with its composition and unit equations; it has no proper map or finite normalization.
- `AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction.systemProperRestrictionCoherence`
  (`Sheaf.Paper.SystemProperRestrictionCoherence`,
  node `lem-sp-system-proper-restriction-coherence`). This is the proper-direct-image factor
  alone, with its composition and unit equations; it has no open map or finite normalization.
- `AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction.systemRestrictionFiniteNormalization`
  (`Sheaf.Paper.SystemRestrictionFiniteNormalization`,
  node `lem-sp-system-restriction-finite-normalization`). This checks only the finite
  normalization of an already constructed normalized comparison, and does not assert its
  existence, coefficient composition or unit equation.

This is a decomposition: one upper hole closed, three lower holes added, net minus two holes
closed. It is not a completed proof independent of `sorry`. Each new theorem has its source
and a full natural-language argument in its docstring. Edge cases considered include identity
coefficient maps, identity/empty opens, zero coefficient rings, nonflat maps and unbounded
complexes. None requires restriction to preserve K-injectives.

## No longer needed

Removed the following direct private imports from the item module:

- `Sheaf.CategoryTheory.SystemRingedSequenceSite`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Sheaf.Paper.SemilinearDerivedSections`
- `Sheaf.CategoryTheory.RestrictionRingedToposModuleDirectImage`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.CategoryTheory.NormalizedDerivedComparisonComposition`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Mathlib.CategoryTheory.Localization.Predicate`

Their mathematical roles remain in the split factor nodes where applicable. No existing
mathematical dependency is claimed globally unnecessary, and no module is withdrawn.
The parent's five former direct `tool_uses` entries are removed:
`lem-weil-pbc-module-sheaves-colimits-forgetful`, `lem-coef-semilinear-derived-sections`,
`lem-weil-pbc-restriction-ringed-topos-module-direct-image`,
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition` and
`lem-sf-open-tensor-normalization`. They describe work inside the factor arguments rather
than tools used directly by the pasting proof. The original public reexports are preserved.

## Where the brief, the DAG or earlier work was wrong

No existing statement was found false. The original plan correctly separates the open,
proper and evaluation arguments, but its generic existing declarations do not directly
produce these specialized records. In particular, ringed-topos derived composition is
stated for small sites and requires transport from the actual sequence sites; the normalized
comparison composition theorem also requires transport from its strict equal-square and
chosen-resolution presentation to the canonical localized restriction functors. The split
proper statement includes these tasks explicitly rather than claiming that the generic
lemma is directly applicable. The finite step separately requires an equality with the
specified adjunction mate, not an inference from equality after evaluation.

The unit `sk-def-sf-operations` and its route are retained. New nodes descend from the
existing compact-support finite-field-independence ancestor through the original parent.
There are no statement or definition repairs, hence no change record or forced adaptations.

## New nodes

`lem-sp-system-open-restriction-coherence`: original proof step 4, ordinary summand comparison,
open-adjunction normalization, exact localization and coefficient composition/unit equations.
Sources: Stacks 03DI and 03DJ. The module is
`lean/Sheaf/Paper/SystemOpenRestrictionCoherence.lean`.

`lem-sp-system-proper-restriction-coherence`: original steps 2, 3 and 6, ringed-site
factorizations, K-injective resolution normalization, proper composition and unit equations.
Sources: Stacks 0D6E and 070Y. The module is
`lean/Sheaf/Paper/SystemProperRestrictionCoherence.lean`.

`lem-sp-system-restriction-finite-normalization`: original step 7, computation of the inverse
proper comparison as an adjunction mate and evaluation of both normalized factors. Sources:
Stacks 03DI, 0D6E and 070Y; Zheng Construction 4.1. The module is
`lean/Sheaf/Paper/SystemRestrictionFiniteNormalization.lean`.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
