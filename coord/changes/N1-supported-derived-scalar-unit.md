# SupportedDerivedScalarUnit

## Reason

Repair of the return on head 2f8caf3265: Status now starts with open.
The current main branch has independently introduced the named exact degree-zero scalar
interface (M9-supported-scalar-unit-named-interface.md). Retain that landed definition
and its public imports verbatim. The earlier packet's proposed Functor.DerivedUnit
replacement is superseded. Instead the two new proof consumers apply the proved
SheafExactDegreeZero.scalarUniversal_derivedUnit API to obtain the raw unbounded
Hom-bijection formula used by the categorical composition lemmas. This new proved API
uses scalarUniversal_iff on the general site, so consumers compare named unit predicates
without unfolding the concrete derived localization data. Both existing definitions
are retained; the representation has an explicit normalization lemma.

## Old

```lean
@[irreducible]
def SupportedDerivedScalarUnit {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G) : Prop :=
  SheafExactDegreeZero.scalarUniversal T.smallEtaleTopology φ F G η
```

## New

The definition above is retained verbatim from current main. There is no delivered change
to OrdinarySupportedKummerScalar or its DAG node. Both proof consumers unfold
SupportedDerivedScalarUnit and apply scalarUniversal_derivedUnit;
their statements are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar | unclaimed | Current source retained verbatim. |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarSource | unclaimed | Existing interface retained. |
| Sheaf.SixFunctors.GeoCartierCoeffExtension | unclaimed | Existing scalarUniversal-based proof retained. |
| Sheaf.AlgebraicGeometry.ScalarUniversalDerivedUnit | N1, new | Proves the canonical interface conversion on a general site. |
| Sheaf.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit | N1, new | Uses the proved scalarUniversal_derivedUnit API. |
| Sheaf.AlgebraicGeometry.CartierEtaleKummerDerivedUnit | N1, new | Uses the proved scalarUniversal_derivedUnit API. |

No target definition changes as a result of this superseded scalar-unit replacement.
The separate Cartier foundation record still describes its own interface changes.

## Status

landed 20261021T012410-L-2185565 2026-10-21 (merge of deliver/N1/Sheaf.AlgebraicGeometry.CartierReductionSiteComparison)
