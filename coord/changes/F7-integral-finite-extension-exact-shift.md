# Finite-extension exact shift and localization descent

## Reason

The former statements asserted exactness for every coherent shift. Coherence alone does not imply preservation of distinguished triangles: multiplying the canonical shift comparison by (-1)^n reverses a nonzero connecting class. For E=L=Q_3 on complete coefficient modules at a point, use the nonsplit sequence Z_3 --3--> Z_3 --> F_3. Its connecting class has order 3, and the triangle with its negative and the first two maps fixed is not distinguished. The blueprint asks for an exact shift to exist.

Construct an exact homotopy functor from the termwise Roos cone, derive it using the resolving-class theorem, and transport its shift to the selected scalar functor using the normalized uniqueness clause. No target statement or existing coefficient definition changes.

## Old

```lean
theorem comparison_precomp_triangulated
    (c : (integralScalarExtensionOfUniverses l E L ι X).CommShift ℤ) :
    let _ := c
    (DerivedCategory.Qh ⋙ integralScalarExtensionOfUniverses l E L ι X).IsTriangulated
```

```lean
theorem comparison_invertibility_triangulated_isTriangulated
    (c : (integralScalarExtensionOfUniverses l E L ι X).CommShift ℤ) :
    (integralScalarExtensionOfUniverses l E L ι X).IsTriangulated
```

## New

```lean
theorem comparison_precomp_triangulated :
    ∃ (c : (integralScalarExtensionOfUniverses l E L ι X).CommShift ℤ),
      letI := c
      (DerivedCategory.Qh ⋙ integralScalarExtensionOfUniverses l E L ι X).IsTriangulated
```

```lean
theorem comparison_invertibility_triangulated_isTriangulated
    (c : (integralScalarExtensionOfUniverses l E L ι X).CommShift ℤ)
    (h : letI := c
      (DerivedCategory.Qh ⋙ integralScalarExtensionOfUniverses l E L ι X).IsTriangulated) :
    letI := c
    (integralScalarExtensionOfUniverses l E L ι X).IsTriangulated
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionTriangulatedPrecomp | F7 | Replace the false arbitrary-shift conclusion by construction of an exact shift. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibilityTriangulated | unclaimed | The only caller of the changed item and the only user of the changed intermediate declaration. Pass both the constructed shift and its precomposition exactness to descent. The final existential declaration keeps its signature verbatim. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility | unclaimed | Direct importer of the adapted parent; uses only its unchanged existential declaration. Compile unchanged against the delivery. |

The downstream scans list 514 and 513 transitive importers, respectively, but only the adapted parent mentions either changed declaration name. There are no public import removals, public instance changes, or edits under lean/WeilConjectures. The parent was unclaimed in both the shared and current server records before adaptation.

## Status

landed 20261028T072412-L-1943251 2026-10-28 (merge of deliver/F7/Sheaf.SixFunctors.CoefIntegralFiniteExtensionTriangulatedPrecomp)
