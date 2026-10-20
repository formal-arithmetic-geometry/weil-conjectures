## What changed

Proved `AlgebraicGeometry.ProEtale.fixSiteOpenExchange` in the assigned module by
lifting the ordinary comparison equation through the exact-functor localization cube.
The generic cube theorem is in `Sheaf.CategoryTheory.DerivedExactCube`. The ordinary
module retains the canonical inverse-unit calculation and imports the specialized
square interface from `Sheaf.AlgebraicGeometry.FixSiteOpenExchangeSquare`.

Validation: the four delivered modules compile, as do the unchanged consumers
`Sheaf.AlgebraicGeometry.CompactSupportOpenFactor` (13.8 seconds) and
`Sheaf.Paper.CompactSupportExchangeTransport` (32.3 seconds), using the packet's
compiled modules. The third direct importer, `EtaleCompactSupportCoefficientChange`,
could not be checked because its unrelated `Sheaf.Paper.ProperCoefficientUniversal`
dependency is absent from the published build. No consumer adaptation was necessary.
The full server dry run and axiom preflight passed at `c6ec7b64f1`; subsequent packet
changes only correct node prose and report the checks.

## Proved and sorry left

Closed 1 of 1 original item holes; added 1 named ordinary-sheaf hole. This is a
decomposition (net 0 holes closed), not a completed proof of the import closure.
The original item theorem is proved from that separate ordinary result:

`AlgebraicGeometry.ProEtale.fixSiteOpenExchange`, node
`lem-fix-site-open-exchange`.

Also proved `CategoryTheory.Functor.mapDerivedCategory_exactCube`, node
`lem-fix-site-open-exchange-localization`, and
`AlgebraicGeometry.ProEtale.fixSiteOpenSheafExchangeIso_unit`.

The specialized square theorem `AlgebraicGeometry.ProEtale.fixSiteOpenExchangeSquare`
(node `lem-fix-site-open-exchange-square`) is also fully proved from the generic
comparison-square component, including the flipped chosen-square normalization.
One strictly separate ordinary comparison result remains as a named public theorem:
`AlgebraicGeometry.ProEtale.fixSiteOpenExchangeSheaf` (node
`lem-fix-site-open-exchange-sheaf`). Its docstring gives the source and complete
mate-calculus proof plan. The four delivered modules compile; there is one syntactic
`sorry`, the whole proof of that public theorem, and no sorry in a definition or
private declaration.

## No longer needed

Removed these proof imports from the assigned module. All original public imports,
including the unit-route site-comparison module, are retained:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`
- `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChangeUnderivedCompatibility`
- `Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`

The strict-tower scalar theorem `lem-cbc-finite-open-exchange-scalars` and the
underived compatibility theorem are not needed by the proved target route. The
remaining ordinary comparison calculation uses the generic comparison-square
component and the specialized square theorem listed above.

## Where the brief, the DAG or earlier work was wrong

The strict-tower scalar interface has different coordinates from the ordinary
fixed-ring sheaves, so the ordinary pro-etale unit formula is obtained directly
from its canonical mate construction. Earlier compiler status overstated validation
of the ordinary comparison proof. The specialized square conversion is now proved.
The final ordinary mate calculation remains separate from the fully proved unbounded
localization and bounded-below restriction argument: it contains no derived objects.
A complete generic adjunction calculation is retained as a proved private helper,
but its concrete specialization has not been validated within the file limit.

## New nodes

`lem-fix-site-open-exchange-square`: the specialized inverse-image comparison square
used by the ordinary exchange calculation; its statement and complete proof are in
`Sheaf.AlgebraicGeometry.FixSiteOpenExchangeSquare`.

`lem-fix-site-open-exchange-localization`: the proved exact-functor localization cube.
`lem-fix-site-open-exchange-sheaf`: the ordinary comparison equation, split from
the derived equation and containing the single remaining named hole.

Change record: `coord/changes/fix-site-open-exchange-localization-helpers.md`.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
