# WeilConjectures.normalizedDVR_scalar_cokernel_comparison

## Reason

Repair the return of delivery `1342efd9745`. The return records that the batch take-out
`a62c78b1fa2` removed this module after base `9feb695b8`, and asks that it be restored.
At the repair checkout, the module and its node are absent, but there is also no
`coord/rework.tsv` row or `quarantine/Sheaf/Paper/NormalizedDVRScalarCokernelComparison.lean`.
The existing claim `coord/claims/Sheaf.Paper.NormalizedDVRScalarCokernelComparison.lock`
is still held by V8. There is therefore no different rework item to claim or quarantine
source to copy. Restore the retained delivered source and node at their original paths;
do not withdraw anything or manufacture a rework row. This record makes the restoration
explicit rather than attempting an unchanged re-push.

The batch take-out also reverted the parent proof plan. Reconcile its current DAG node
by citing the restored comparison in the scalar-cokernel step. The parent's Lean
statement and proof are untouched; this is a dependency restoration for its unfinished
proof. No source-library file, target statement, existing public signature, public
import, instance or non-theorem body is changed.

## Old

The module and node are absent from the current library and quarantine; the retained
returned delivery had the following public theorem statement, unchanged here:

```lean
theorem normalizedDVR_scalar_cokernel_comparison
    {m n : ℕ} (h : n ≤ m)
    (i : normalizedDVRModuleRes l E X h ⋙ completedIntegralRestrictScalars l E X D hl m ≅
      completedIntegralRestrictScalars l E X D hl n)
    (F : CochainComplex (normalizedDVRModules l E X m) ℤ)
    (K : CochainComplex (normalizedDVRModules l E X n) ℤ)
    (f : F ⟶ ((normalizedDVRModuleRes l E X h).mapHomologicalComplex (.up ℤ)).obj K)
    (hF : CochainComplex.IsKFlatIndependentCoefficients F)
    (hf : ∀ Z : normalizedDVRDerived l E X n,
      Function.Bijective (fun b : DerivedCategory.Q.obj K ⟶ Z ↦
        (DerivedCategory.Q.map f ≫
          (normalizedDVRModuleRes l E X h).mapDerivedCategoryFactors.inv.app K) ≫
          (normalizedDVRRes l E X h).map b))
    (hz : ((⟨(PrincipalKoszulStrictReplacement.uniformizer l E X).val,
        (PrincipalKoszulStrictReplacement.uniformizer l E X).property⟩ :
      RingCat.sectionsSubring ((completedIntegralCommRingSheafUnrestricted l E X).obj ⋙
        forget₂ CommRingCat RingCat)) ^ (n + 1) •
        𝟙 (((completedIntegralRestrictScalars l E X D hl m).mapHomologicalComplex
          (.up ℤ)).obj F)) ≫
      (((completedIntegralRestrictScalars l E X D hl m).mapHomologicalComplex
        (.up ℤ)).map f ≫ (Functor.mapHomologicalComplexCompIso
          i (.up ℤ)).hom.app K) = 0) :
    QuasiIso (cokernel.desc ((⟨(PrincipalKoszulStrictReplacement.uniformizer l E X).val,
        (PrincipalKoszulStrictReplacement.uniformizer l E X).property⟩ :
      RingCat.sectionsSubring ((completedIntegralCommRingSheafUnrestricted l E X).obj ⋙
        forget₂ CommRingCat RingCat)) ^ (n + 1) •
        𝟙 (((completedIntegralRestrictScalars l E X D hl m).mapHomologicalComplex
          (.up ℤ)).obj F))
      (((completedIntegralRestrictScalars l E X D hl m).mapHomologicalComplex
        (.up ℤ)).map f ≫ (Functor.mapHomologicalComplexCompIso
          i (.up ℤ)).hom.app K) hz)
```

## New

Restore the same public theorem statement above, with its completed proof from
`1342efd9745`, and the matching retained node. The parent node
`lem-coef-normalized-dvr-flat-cokernel` now cites this comparison in the step that
uses the universal derived finite-level transition to identify the scalar cokernel.
No Lean consumer adaptation is necessary because the public interface is preserved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NormalizedDVRScalarCokernelComparison | V8 | Restore the proved item and its node. |
| Sheaf.Paper.NormalizedDVRFlatCokernel | unclaimed at repair inspection | Restore only its DAG proof dependency on the item; no Lean edit. |

## Status

landed 20261026T083346-L-2332223 2026-10-26 (merge of deliver/V8/Sheaf.Paper.NormalizedDVRScalarCokernelComparison)
