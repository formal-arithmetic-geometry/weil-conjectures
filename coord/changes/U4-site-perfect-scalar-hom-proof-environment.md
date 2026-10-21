# Sheaf.Algebra.Homology.SitePerfectScalarHomComparison proof environment

## Reason

The new private categorical proofs use monoidal notation and keep the generator and
normalization predicates folded during constructor elaboration. One private model
constructor temporarily unfolds the ordinary sheaf monoidal instance. The static
command scan requests a record for these elaboration commands. Every original public
signature, definition body and public import is preserved verbatim.

## Old

```lean
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
```

There was no local attribute for `SiteScalarHomGeneratorFormula` or
`SiteScalarHomTensorNormalization`, and no private source-duality model constructor.
The existing local irreducibility command for `SheafOfModules.monoidalCategory` and
`derivedInternalHomOfUniverses` is preserved.

## New

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
attribute [local irreducible] SiteScalarHomGeneratorFormula SiteScalarHomTensorNormalization
```

The private `siteScalarSourceDualityModel` constructor is preceded by:

```lean
attribute [local semireducible] SheafOfModules.monoidalCategory in
```

The open command controls notation resolution in this file. Both irreducibility
attributes are local, and the semireducibility command applies only to the following
private declaration. None changes a definition, exported instance, or target statement.
The new public results and their source arguments are recorded in the two new nodes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.SitePerfectScalarHomComparison | U4 | Private proof elaboration only. |

There are no current direct Lean importers of the item in either library root.
Its unfinished DAG parents retain the same public statements and definitions; no
consumer adaptation is required. No other group's file is changed.

## Status

landed 20261021T144009-L-35035 2026-10-21 (merge of deliver/U4/Sheaf.Algebra.Homology.SitePerfectScalarHomComparison)
