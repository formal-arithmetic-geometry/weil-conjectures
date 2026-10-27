## What changed

Proved `WeilConjectures.PurityFiniteSetting.diagonalEtaleRhoUnitSquare` with its existing signature. The proof identifies the normalized tensor locality with structural locality, restricts the Cartesian base-change/locality identity along the canonical open lift from arbitrary `O`, transports through the fixed site comparison, applies naturality to coefficient-unit change, and cancels the common restricted dualizing comparison.

Added private, proved helpers and private proof imports in the item module. After improving the local open-comparison definition and categorical pasting, extracted two fully proved parts into `Sheaf.Paper.DiagonalEtaleLocalityUnitChange` and `Sheaf.Paper.ComparisonPullbackRestrictionCoherence`: coefficient-unit naturality and restriction coherence of the fixed site comparison. This reduces the per-file compile time without adding holes. Updated its node's proof route and dependencies. No existing definitions or statements were changed. The proof imports `SectionExceptionalFibreCoherence`, `DiagonalEtaleSourceEndpoint`, `PuritySectionRestrictionEtaleFunctorial`, `PuritySectionBaseComparisonLaws`, and `ComparisonPullbackDerivedCoherence` for their existing coherence APIs, and the two new proved modules. Private `import all` declarations for Mathlib `Limits.HasLimits` and `Logic.Small.Defs` expose the implementation definitions needed to align the recorded derived-functor instances; transparency checking remains enabled.

The generic identity `Etale.structural_locality_baseChange` and pullback coherence helpers are taken from `Sheaf.Paper.SectionExceptionalFibreCoherence` (node `lem-trf-section-exceptional-fibre-coherence`, unit `sk-i-curve-zero`). Only generic six-functor mate/pasting identities are used, not that unit's curve theorem; the smooth-purity unit route is preserved.

## Proved and sorry left

Closed the one original hole in `WeilConjectures.PurityFiniteSetting.diagonalEtaleRhoUnitSquare` (node `lem-pur-diagonal-etale-rho-unit-square`). Also proved `WeilConjectures.PurityFiniteSetting.diagonalEtaleLocality_unitChange` (node `lem-pur-diagonal-etale-locality-unit-change`) and `WeilConjectures.PurityFiniteSetting.diagonalEtaleComparison_restriction` (node `lem-pur-comparison-pullback-restriction-coherence`). Added zero holes and split off zero unproved statements. No `sorry` remains in the delivery.

Validation: all three production modules compile without errors or warnings and pass the 60-second per-file gate through `lcompile.py`. The target axiom print lists `propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx`; the delivery itself contains no admitted theorem. The separate axiom probe passes; no other axiom is reported. The dependency scan of imported proof bodies did not expose the underlying admitted declaration names, so no claim is made that the transitive proof closure is admission-free.

## No longer needed

No existing imports were removed. The original direct proof dependencies `lem-amb-etale-left-comparison-base-change`, `lem-pur-diagonal-base-change`, and `def-pur-etale-exceptional-precomp-locality` are replaced by the existing proved structural locality and comparison coherence APIs. Their modules are not claimed to be globally unused: definitions and other source-library proofs may still import them. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned compatibility already follows from proved generic private helpers in existing modules: `structural_locality_baseChange`, `source_comp_eq`, `sourceEtale_locality_congr`, and `locality_tensorMate`. No further split is needed for this item. For arbitrary `O`, the canonical lift to the full inverse image is an open immersion; it need not itself be a Cartesian source square.

## New nodes

`lem-pur-diagonal-etale-locality-unit-change`: the fully proved compatibility of normalized etale locality with monoidal-unit/degree-zero coefficient change. This is one strict part of the original argument and has no target-open rho, source span, dimension or DNC comparison. Its separate module avoids repeatedly checking the dependent equality-congruence proof in the larger rho-square module. No change record is needed: only the item module and the new modules/nodes are changed.

`lem-pur-comparison-pullback-restriction-coherence`: the fully proved composition coherence of the fixed site comparison with an arbitrary open square. It assumes no dualizing object, smoothness, dimension or normalized exceptional pullback and is strictly simpler than the item. Its separate module keeps compositor checking outside the main proof file.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
