# AlgebraicGeometry.tensorResolutionChartRestrictionComplexIso

## Reason

Restore the quarantined zero-hole module from coord/rework.tsv. Its archived imports
mix Sheaf tensor-naturality declarations with the adopted source declarations now
re-exported by Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonNaturality.
Compiling the unchanged archive fails at its imports:

```
import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTensorNaturality failed,
environment already contains 'AlgebraicGeometry.TensorResolutionTensorNaturality_localInst1'
from Sheaf.AlgebraicGeometry.QCohTensorResolutionTensorNaturality
```

The adopted source TotalCoherence module already contains the same componentwise
restriction isomorphism and both fully proved coherence identities. Re-export it
from the restored Sheaf path instead of loading and redeclaring the duplicate
helper chain. No source-library file is edited, and no archive is deleted.

## Old

The full quarantined module, including the original definition and theorem signatures:

```lean
module
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionRestrictionCoherence
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionTotalComponents
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonNaturality

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionTotalCoherence_localInst1 (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance TensorResolutionTotalCoherence_localInst2 (X : Scheme.{u}) : MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance TensorResolutionTotalCoherence_localInst3 (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionTotalCoherence_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- The componentwise identification of two successive chart restrictions. -/
noncomputable def tensorResolutionChartRestrictionComplexIso (Y : Scheme.{u})
    (V U : Y.affineOpens) (h : V.1 ≤ U.1) (E : CochainComplex Y.Modules ℤ) :
    ((Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op))).mapHomologicalComplex
      (.up ℤ)).obj (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj E) ≅
    ((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj E :=
  (Functor.mapHomologicalComplexCompIso (tensorResolutionChartRestrictionIso Y V U h) (.up ℤ)).app E

/-- Inverse total tensor comparisons respect successive affine restrictions. -/
theorem tensorResolutionChartRestriction_total_inv (Y : Scheme.{u})
    (V U : Y.affineOpens) (h : V.1 ≤ U.1) (E F : CochainComplex Y.Modules ℤ) :
    let RU := (Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let RV := (Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let R := (Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op))).mapHomologicalComplex (.up ℤ)
    HomologicalComplex.mapBifunctorMap
        (tensorResolutionChartRestrictionComplexIso Y V U h E).hom
        (tensorResolutionChartRestrictionComplexIso Y V U h F).hom
        (curriedTensor (Spec Γ(Y, V.1)).Modules) (.up ℤ) ≫
        (tensorResolutionRestrictionTotalIso V.2.fromSpec E F).inv =
      (tensorResolutionRestrictionTotalIso (Spec.map (Y.presheaf.map (homOfLE h).op))
        (RU.obj E) (RU.obj F)).inv ≫
        R.map (tensorResolutionRestrictionTotalIso U.2.fromSpec E F).inv ≫
        (tensorResolutionChartRestrictionComplexIso Y V U h
          (CochainComplex.mapBifunctor E F (curriedTensor Y.Modules))).hom := by
  dsimp only
  ext i : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f]
  rw [tensorResolution_ι_totalTensorMap_assoc,
    tensorResolution_ι_restrictionTotal_inv,
    tensorResolution_ι_restrictionTotal_inv_assoc]
  rw [Functor.mapHomologicalComplex_map_f]
  rw [← Functor.map_comp_assoc]
  rw [tensorResolution_ι_restrictionTotal_inv]
  simp only [Functor.map_comp, Category.assoc]
  change _ = _ ≫ _ ≫
    (Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op))).map
        ((Scheme.Modules.restrictFunctor U.2.fromSpec).map
          (HomologicalComplex.ιMapBifunctor E F (curriedTensor Y.Modules) (.up ℤ) p q i hpq)) ≫
      (tensorResolutionChartRestrictionIso Y V U h).hom.app _
  have hnat := (tensorResolutionChartRestrictionIso Y V U h).hom.naturality
    (HomologicalComplex.ιMapBifunctor E F (curriedTensor Y.Modules) (.up ℤ) p q i hpq)
  simp only [Functor.comp_map] at hnat
  rw [hnat]
  change (((tensorResolutionChartRestrictionIso Y V U h).hom.app (E.X p)) ⊗ₘ
      ((tensorResolutionChartRestrictionIso Y V U h).hom.app (F.X q))) ≫
      (tensorResolutionRestrictionTensor V.2.fromSpec (E.X p) (F.X q)).inv ≫ _ = _
  rw [reassoc_of% tensorResolutionChartRestriction_tensor_inv]
  rfl

/-- Forward total tensor comparisons respect successive affine restrictions. -/
theorem tensorResolutionChartRestriction_total (Y : Scheme.{u})
    (V U : Y.affineOpens) (h : V.1 ≤ U.1) (E F : CochainComplex Y.Modules ℤ) :
    let RU := (Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let RV := (Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let R := (Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op))).mapHomologicalComplex (.up ℤ)
    R.map (tensorResolutionRestrictionTotalIso U.2.fromSpec E F).hom ≫
        tensorResolutionRestrictionTensorMap (Spec.map (Y.presheaf.map (homOfLE h).op))
          (RU.obj E) (RU.obj F) (RV.obj E) (RV.obj F)
          (tensorResolutionChartRestrictionComplexIso Y V U h E).hom
          (tensorResolutionChartRestrictionComplexIso Y V U h F).hom =
      (tensorResolutionChartRestrictionComplexIso Y V U h
        (CochainComplex.mapBifunctor E F (curriedTensor Y.Modules))).hom ≫
          (tensorResolutionRestrictionTotalIso V.2.fromSpec E F).hom := by
  dsimp only [tensorResolutionRestrictionTensorMap]
  apply (cancel_mono (tensorResolutionRestrictionTotalIso V.2.fromSpec E F).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [tensorResolutionChartRestriction_total_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

end AlgebraicGeometry
```

## New

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalCoherence

/-! # Total tensor comparisons under successive affine restrictions

Compatibility import for `AlgebraicGeometry.tensorResolutionChartRestrictionComplexIso`,
`AlgebraicGeometry.tensorResolutionChartRestriction_total_inv`, and
`AlgebraicGeometry.tensorResolutionChartRestriction_total`.

The source module supplies the componentwise restriction isomorphism and the same two proved
coherence identities. Re-exporting it avoids mixing the Sheaf and source copies of their
common tensor-naturality dependencies.
-/

@[expose] public section
```

The names and mathematical types of all three declarations are preserved. The
source spelling `_RV` instead of unused `RV` in the inverse theorem is an unused
let-binding rename. The definition uses exactly the same
`Functor.mapHomologicalComplexCompIso` component. Both theorem statements are
checked against the archived types by direct applications in a scratch compile.
The existing source proofs retain the total-summand calculation, restriction
naturality, and cancellation argument; this changes no mathematical dependency.

## Users

The absent module has no live Lean importers (`tools/downstream.py` reports it
unknown). A separate full-text search includes quarantined users rather than
assuming the mathematics is unused. Each user below still receives all three
identically named declarations at the same types. No user is withdrawn or adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.QCohTensorResolutionTotalCoherence | F1 | Restored as a public compatibility import. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartAugmentationNaturality | unclaimed, quarantined | Same three declarations remain available; no signature change. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensorTransport | unclaimed, quarantined | Same three declarations remain available; no signature change. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionHomologyCoherence | unclaimed, quarantined | Same three declarations remain available; no signature change. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartHomologyNaturality | unclaimed, quarantined | Same three declarations remain available; no signature change. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensorPositiveNaturality | unclaimed, quarantined | Same three declarations remain available; no signature change. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartSummandNaturality | unclaimed, quarantined | Same three declarations remain available; no signature change. |

The parent node new-t3-qcoh-tensor-resolution-chart-comparison-naturality explicitly
uses `tensorResolutionChartRestriction_total` in step 3. Its statement, dependency
records and route remain applicable. No DAG node has its Lean attachment at this
helper module, so there is no attachment to move or remove. No unit route or target
signature changes. There are no forced adaptations.

## Status

landed 20261022T044012-L-1171957 2026-10-22 (merge of deliver/F1/Sheaf.AlgebraicGeometry.QCohTensorResolutionTotalCoherence)
