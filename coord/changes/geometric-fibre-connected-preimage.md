# AlgebraicGeometry.Scheme.Hom.isConnected_geometricFibre_preimage

## Reason

Expose only the single-piece geometric connectedness step of the Stein splitting argument.
This new theorem assumes a geometrically connected map and a purely inseparable singleton
fibre; it makes no assertion of the existence of an étale neighbourhood or a partition.
The existing item signature is unchanged. No existing definition or statement is altered.

## Old

No declaration. The single-piece step was included in the proof plan of
`AlgebraicGeometry.Scheme.Hom.exists_etale_geometricFibre_clopen_partition`.

## New

```lean
theorem Scheme.Hom.isConnected_geometricFibre_preimage
    {X T U : Scheme.{u}} (q : X ⟶ T) [GeometricallyConnected q]
    (r : T ⟶ U) (p : X ⟶ U) (h : q ≫ r = p) (u : U) (V : T.Opens)
    (hv : ∃ v : V.toScheme, (V.ι ≫ r) v = u ∧
      (∀ w : V.toScheme, (V.ι ≫ r) w = u → w = v) ∧
      @IsPurelyInseparable (U.residueField ((V.ι ≫ r) v))
        (V.toScheme.residueField v) _ _ ((V.ι ≫ r).residueFieldMap v).hom.toAlgebra) :
    _root_.IsConnected
      ((pullback.fst p
        (Spec.map (CommRingCat.ofHom
          (algebraMap (U.residueField u) (AlgebraicClosure (U.residueField u)))) ≫
            U.fromSpecResidueField u)) ⁻¹' (q ⁻¹' (V : Set T)))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProperGeometricFibreClopenPartition | F4 | Private proof import; applies the new theorem to each intermediate Stein clopen. Existing public signature unchanged. |

No existing module imports the new module. The item is its sole user in this delivery.

## Status

landed 20261025T163619-L-726238 2026-10-25 (merge of deliver/F4/Sheaf.AlgebraicGeometry.ProperGeometricFibreClopenPartition)
