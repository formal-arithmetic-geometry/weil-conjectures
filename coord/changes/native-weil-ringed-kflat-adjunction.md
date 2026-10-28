# AlgebraicGeometry.ProEtaleWeilSheaf.native_weil_tensor_ringed_kflat_flat

## Reason

The flat-field extraction from NativeWeilRingedTensorKFlatData dropped its existing
underived tensor-Hom adjunction. The internal-Hom comparison in b does not identify
an arbitrary additive T with the ringed tensor. Both the proved underived comparison
and the existing total comparison require that adjunction. Restore it as an explicit
argument, then prove transport by pulling acyclic tests through the inverse equivalence.
This follows the actual tensor of the source and the unchanged parent interface.
No target signature or definition changes.

## Old

```lean
theorem native_weil_tensor_ringed_kflat_flat :
    ∀ (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ),
      NativeTensorKFlat k₀ l X T P →
        CochainComplex.IsKFlatIndependentCoefficients (R := b.R)
          ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P)
```

The old proof import was Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients.

## New

```lean
theorem native_weil_tensor_ringed_kflat_flat (adj : T ⊣₂ ihomBifunctor k₀ l X) :
    ∀ (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ),
      NativeTensorKFlat k₀ l X T P →
        CochainComplex.IsKFlatIndependentCoefficients (R := b.R)
          ((b.native.functor.mapHomologicalComplex (.up ℤ)).obj P)
```

The proof imports Sheaf.Paper.NativeWeilTensorRingedChainData and
WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex instead.
The public import of BridgeData is unchanged. The proof uses the underived comparison,
the total comparison at the canonical Koszul sign, exactness of the equivalence and its
inverse, the counit, and invariance of ExactAt under isomorphism. The single caller
passes its existing adj argument. No other declaration or instance changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NativeWeilTensorRingedKFlatFlat | K8 | Restores adj and proves the corrected statement. |
| Sheaf.Paper.NativeWeilTensorRingedKFlatData | unclaimed | The only direct importer and external name user: adds adj to its existing application; all signatures stay identical. |

The downstream scan found these two name users among 139 reachable modules.
The unchanged original KFlatData compiled against the new theorem fails at line 57:
`native_weil_tensor_ringed_kflat_flat b T` has an extra `adj` argument and cannot fill
its `flat` field. The adaptation is exactly `native_weil_tensor_ringed_kflat_flat b T adj`.
All further consumers see the identical KFlatData interface.

The DAG citer lem-sf-native-weil-tensor-ringed-kflat-localization is not a Lean importer.
Its unfinished plan also needs the native ringed data and adjunction restored before
it can use this theorem; this is recorded with holds:false in statement_change.

## Status

landed 20261028T020548-L-2524635 2026-10-28 (merge of deliver/K8/Sheaf.Paper.NativeWeilTensorRingedKFlatFlat)
