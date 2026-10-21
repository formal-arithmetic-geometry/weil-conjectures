# Public import interface for PerfectUniversalLowestCohomologyPullback

## Reason

The quarantined source imported a withdrawn empty Sheaf bridge, while the public
statement refers to the upstream derived pullback and tensor pullback declarations.
The restored theorem therefore needs the upstream public interfaces to elaborate.

## Old

`PerfectUniversalLowestCohomologyPullback.lean` publicly imported
`Sheaf.AlgebraicGeometry.DerivedPullback`; that module is now an intentionally empty
withdrawal and exports no `derivedPullback` or `Modules.tensorPullback` declarations.

## New

The module publicly imports `WeilConjectures.AlgebraicGeometry.DerivedPullback` and
`WeilConjectures.AlgebraicGeometry.TensorPullback`. The theorem statement, declaration
name, universes, and proof conclusion are unchanged.

## Users

The module's direct importers see the same theorem declaration. The added upstream
imports only make the declarations already present in its public signature available;
no downstream theorem or signature requires adaptation.

## Status

landed 20261021T012401-L-2183879 2026-10-21 (merge of deliver/G4/Sheaf.AlgebraicGeometry.PerfectUniversalLowestCohomologyPullback)
needed before landing.
