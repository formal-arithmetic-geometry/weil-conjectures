# Comparison definitions shared by the two compatibility statements

## Reason

The counit and square compatibility statements need the five fixed comparison definitions,
while the original theorem needs these statements. Move the unchanged definitions to a
shared module to avoid the resulting import cycle.

## Old

The five definitions were declared in
`WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`:
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonPlusIso`,
`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso'`,
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarComparisonIso`,
`AlgebraicGeometry.ProEtale.baseChangeSourceComparisonIso`, and
`AlgebraicGeometry.ProEtale.baseChangeTargetComparisonIso`.

## New

The definitions have identical names, types, universes, visibility and construction bodies,
in `Sheaf.SixFunctors.ProEtale.BaseChange.SmoothBaseChangeComparisons`.
The original module publicly imports that module. The two new compatibility theorem modules
publicly import it because their statements refer to the definitions. The original module
imports those two theorem modules only for its proof. No target signature, data or
mathematical meaning changes.

## Users

The following original consumers were compiled unchanged against the sandbox overlay:

- `WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekBaseChange`: the source and target
  comparison isomorphisms retain their definitions and types.
- `WeilConjectures.SixFunctors.ProEtale.Derived.Stability`: the right-derived direct-image
  comparison remains available through the original public import.
- `WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension`: the same comparison
  retains its construction and type.
- `WeilConjectures.WeilSheaf.PoincareDuality`: the same comparison retains its construction
  and type.
- `WeilConjectures`: the root module imports the item; its public exports are preserved.
  This aggregate root is left for the maintainer's global build.

No existing consumer needs adapted lines. The item is held by G1; no module held by another
group is changed. The new `ComparisonCounit` and `ComparisonSquare` modules use the shared
comparisons directly, and compiled with the item as one sandbox import graph.

## Status

landed 20261016T135931-L-3400934 2026-10-16 (merge of deliver/G1/WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange)
sandbox modules compiled successfully. The target statements retain exactly their meaning.
