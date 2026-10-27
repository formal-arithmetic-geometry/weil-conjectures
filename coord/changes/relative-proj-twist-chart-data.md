# Relative Proj twist chart data declarations

## Reason

The chart data declarations were moved into the new compatibility module so they have a
definition-node owner.  The target keeps the same public names through its own public import of that module.

## Old

`twistChartOpen`, `twistChartFraction`, and `twistChartRead` were public declarations in
`Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescent`, whose public imports directly
included `TensorPullbackSectionAdjunction`, `RelativeProj.Basic`, and `Twist.UnitToTwist`.

## New

The three declarations are public declarations in
`Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescentCompatibility`; the target and the
object component publicly import that module (the target imports the object and transition
components only for its proof).  Their signatures and bodies are unchanged.  The same module
defines `TwistChartCompatibility`, which records the normalized scalar-extension comparison
and its commuting chart square.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.RelativeProjTwistChartFractionAdd | other | public names remain available through the target's import |
| Sheaf.AlgebraicGeometry.SymmetricProjAffineGeneratorLinear | other | public names remain available through the target's import |
| Sheaf.AlgebraicGeometry.SymmetricProjGluedSections | other | public names remain available through the target's import |
| Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescent | J1 | imports the compatibility module publicly, the two components privately |

## Status

landed 20261027T234009-L-4159809 2026-10-27 (merge of deliver/J1/Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescent)
