# WeilConjectures.commonStageTensor_triangle

## Reason

The right-unit comparison follows from the left-unit comparison and
associativity by the triangle identity for the prescribed common-stage tensor.
No exact public declaration for that triangle existed. The new theorem isolates
it for the existing maps; it adds no alternate tensor or coherence structure.

## Old

No declaration `WeilConjectures.commonStageTensor_triangle`.

## New

```lean
theorem commonStageTensor_triangle
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (A B : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    (pullbackTensorCommonAssociator l Ω X A (pullbackTensorCommonUnit l Ω X) B).hom ≫
        (commonStageDerivedTensor l Ω X).map
          (Prod.mkHom (𝟙 A) (pullbackTensorCommonLeftUnitor l Ω X B).hom) =
      (commonStageDerivedTensor l Ω X).map
        (Prod.mkHom (pullbackTensorCommonRightUnitor l Ω X A).hom (𝟙 B))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CommonStageTensorTriangle | G2 (new module) | Isolates the prescribed triangle as one named pending theorem. |
| Sheaf.Paper.AdicCompletedTensorCommonLiftConstraintsRightUnit | G2 | Private proof import; existing public signatures preserved. |

No existing module besides the assigned item changes. Existing consumers of the
item retain its exact interface. The separate arbitrary-data normalization
disputes on left unitality and associativity remain explicitly recorded.

## Status

landed 20261028T081740-L-2777495 2026-10-28 (merge of deliver/G2/Sheaf.Paper.AdicCompletedTensorCommonLiftConstraintsRightUnit)
