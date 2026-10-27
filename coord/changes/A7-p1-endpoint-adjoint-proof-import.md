# AlgebraicGeometry.Etale.p1KummerScalarEndpointExistence proof dependency

## Reason

The unclaimed endpoint-existence module fails to compile in the current overlay at its
private `derivedInsertion_isIso` proof: `SheafExactDegreeZero.isIso_scalarAdjointInsertion`
is unknown. A direct private import makes the helper available; unfolding the insertion
wrapper then identifies the expected arrow with its adjunction transpose. This preserves
every declaration signature, attribute and construction and adds no holes. This is an
unclaimed proof repair, not a forced edit of another group's item.

## Old

```lean
private theorem derivedInsertion_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G)
    (hη : SupportedDerivedScalarUnit φ T F G η) :
    IsIso (p1KummerDerivedInsertion φ T η) := by
  unfold SupportedDerivedScalarUnit at hη
  exact SheafExactDegreeZero.isIso_scalarAdjointInsertion T.smallEtaleTopology φ η hη
```

## New

Add the proof import:

```lean
import all Sheaf.CategoryTheory.ExactDegreeZeroAdjoint
```

The private proof is:

```lean
  unfold p1KummerDerivedInsertion
  unfold SupportedDerivedScalarUnit at hη
  exact SheafExactDegreeZero.isIso_scalarAdjointInsertion T.smallEtaleTopology φ η hη
```

## Users

`tools/downstream.py Sheaf.Paper.P1KummerScalarEndpointExistence` reports two downstream
modules. Their interfaces and constructions are unchanged; no adaptation is necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.P1KummerScalarEndpointExistence | unclaimed | Private proof import and unfolding repair only. |
| Sheaf.Paper.P1KummerDerivedScalar | no claim found | Same public theorem signature and proof meaning; no adaptation. |
| Sheaf.Paper.VectorTraceScalarDescent | no claim found | Same transitive public interface; no adaptation. |
| Sheaf.Paper.SupportedRootScalarSiteComparison | A7 | New proof uses the repaired existing endpoint theorem. |

## Status

landed 20261025T163537-L-692667 2026-10-25 (merge of deliver/A7/Sheaf.Paper.SupportedRootScalarSiteComparison)
