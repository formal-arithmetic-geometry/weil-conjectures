# Extract diagonal counit comparison data

## Reason

The two geometric lemmas used by DiagonalAffineCounitRestriction need its explicit
comparison maps without creating an import cycle. Move the data to a separate
module which the original module publicly reexports.

## Old

comparisonPull, restriction, unitChange and coordinate were defined in
Sheaf.Paper.DiagonalAffineCounitRestriction.

## New

The four definitions have identical signatures, attributes and bodies in
Sheaf.Paper.DiagonalCounitComparisonData. The original module publicly imports it.
Add restrictionAlong (the same compositor for an arbitrary commuting open square)
and localInverse (the four-factor inverse with its existing coefficient endpoints).
Both are explicit constructions, with no choice from an existence theorem.

The assigned theorem keeps its exact statement and is proved from two new named
geometric lemmas. The source library WeilConjectures is untouched. The moved
definitions' DAG attachments belong to the new data node; the original node retains
the theorem. No declarations are withdrawn.

## Users

`Sheaf.Paper.DiagonalOrdinaryOrientationNormalization` is the sole direct importer
and the sole external user of the qualified OrientationCounit declarations.
It still sees the same public names, signatures, attributes and constructions.
Its statement and proof need no adaptation.

The downstream textual scan additionally matches the following modules on the
short names restriction or coordinate, including unrelated names in other
namespaces. They retain the same publicly reexported API; no adaptation is needed:

- `Sheaf.Paper.AffineTowerIntegrationSiteTransport`
- `Sheaf.Paper.ChartExceptionalMateCoherence`
- `Sheaf.Paper.ClopenExceptionalScalarDescent`
- `Sheaf.Paper.ClopenSystemFiniteRealization`
- `Sheaf.Paper.EvenLineProductIntegrationMaps`
- `Sheaf.Paper.FieldExtensionIntegralCoordinates`
- `Sheaf.Paper.FieldExtensionReductionLimits`
- `Sheaf.Paper.GeneralChartComparisons`
- `Sheaf.Paper.IntegralReconstructionComparisons`
- `Sheaf.Paper.LineZeroClassExchange`
- `Sheaf.Paper.LocalizedFlagProduct`
- `Sheaf.Paper.SupportedCartierDerivedPullback`
- `Sheaf.SecSmoothPurity.NestedAffineOrientation`

All transitive importers retain the public API. No target statement or used
definition changes meaning, and no consumer is changed in this delivery.

## Status

landed 20261026T023000-L-510496 2026-10-26 (merge of deliver/C6/Sheaf.Paper.DiagonalAffineCounitRestriction)
