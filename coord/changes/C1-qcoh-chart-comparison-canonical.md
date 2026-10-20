# AlgebraicGeometry.tensorResolutionChartComparisonIso

## Reason

The assigned module was quarantined by the 2026-10-20 upstream sync. Its preserved
implementation imports Sheaf tensor-resolution twins alongside source modules,
which fails on duplicate AlgebraicGeometry.isKFlat_tilde. Restoring its bytes
would restore that error. The source library now supplies the complete specified
chart comparison and the same four-map common-resolution construction.

Restore the Sheaf module as a public re-export of that canonical implementation.
This retains its module path and the public comparison declaration, rather than
withdrawing either the module or the mathematics. No upstream file is modified.

The archived consumers spell K-flatness IsAcyclicTensorKFlat; upstream spells the
identical acyclic-tensor condition IsKFlatTensor. A consumer check with the
archived single-chart formula exposed this change as an unknown-identifier error.
Migrate the entire affected archived consumer component in the same delivery.
Seven consumer modules can re-export complete source counterparts. The eighth,
QCohTensorResolutionCoordinateChartIso, retains the same chart comparison, using canonical imports and IsKFlatTensor.
It is constructed from the canonical full-coordinate isomorphism followed by
restriction/homology normalization. The source full-coordinate definition ends
in inverse normalization, so associativity and inverse cancellation identify
this with the original chart-homology/comparison composite. This bundled form
avoids a 60-second elaboration timeout on the original composite. Its local instance names
are made specific to that module to avoid clashes with the canonical full
coordinate construction.

The predicates have exactly the same definition: for every acyclic complex F,
the total tensor complex F tensor K is acyclic. Neither boundedness,
quasi-coherence nor any other hypothesis is changed. The source and archived
comparison definitions use the same chart augmentation and restricted q and s,
with the same order of the four homology maps. The defining-formula consumer is
checked by reflexivity with the canonical spelling. A separate Lean check
proves that the retained chart helper followed by inverse normalization is
exactly the canonical full-coordinate isomorphism, by associativity and inverse
cancellation. The source factorization theorem then identifies the helper with
the original direct composite. A combined consumer imports all nine restored
modules together; all nine main APIs have only the three permitted axioms.

Five existing DAG lean records are reattached to the matching source declarations;
their mathematical statements and dependency/proof plans are retained. There is
no DAG node attached to the item module itself or to the chart-coordinate helper.
No unit route or target signature changes. The mathematical comparison and all
definitions it composes retain their meanings; this is a duplicate-API migration,
so it does not change what the targets assert.

## Old

The item source is preserved in
quarantine/Sheaf/AlgebraicGeometry/QCohTensorResolutionChartComparisonIso.lean:

~~~lean
module
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartModel
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionComparison
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionKFlatBundledRing

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- Compare the chart resolution with a fixed global K-flat resolution after restriction. -/
noncomputable def tensorResolutionChartComparisonIso
    (Y : Scheme.{u}) (M N : Y.Modules) [M.IsQuasicoherent]
    (U : Y.affineOpens) (MA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (P : ProjectiveResolution MA) (K F : CochainComplex Y.Modules ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj M)
    (s : F ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj N)
    (hK : CochainComplex.IsAcyclicTensorKFlat (R := Y.sheaf) K)
    (hF : CochainComplex.IsAcyclicTensorKFlat (R := Y.sheaf) F)
    (hq : QuasiIso q) (hs : QuasiIso s) (i : ℤ) :
    (CochainComplex.mapBifunctor (tensorResolutionChartComplex U MA P)
      (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor Y.Modules 0).obj N))
      (curriedTensor (Spec Γ(Y, U.1)).Modules)).homology i ≅
    (CochainComplex.mapBifunctor
      (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj K)
      (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor Y.Modules 0).obj N))
      (curriedTensor (Spec Γ(Y, U.1)).Modules)).homology i := by
  let R := Scheme.Modules.restrictFunctor U.2.fromSpec
  let RC := R.mapHomologicalComplex (.up ℤ)
  let E := tensorResolutionChartComplex U MA P
  let M0 := (CochainComplex.singleFunctor Y.Modules 0).obj M
  let N0 := (CochainComplex.singleFunctor Y.Modules 0).obj N
  let r := tensorResolutionChartAugmentation M U MA sM P
  have hE : CochainComplex.IsAcyclicTensorKFlat (R := (Spec Γ(Y, U.1)).sheaf) E :=
    tensorResolution_isKFlat_bundledRing Γ(Y, U.1) MA P
  have hK' := isKFlat_restrict U.2.fromSpec K hK
  have hF' := isKFlat_restrict U.2.fromSpec F hF
  have : QuasiIso q := hq
  have : QuasiIso s := hs
  have hq' : QuasiIso (RC.map q) := by dsimp [RC, R]; infer_instance
  have hs' : QuasiIso (RC.map s) := by dsimp [RC, R]; infer_instance
  exact tensorResolutionComparison (Spec Γ(Y, U.1)).sheaf E (RC.obj K) (RC.obj M0)
    (RC.obj F) (RC.obj N0) r (RC.map q) (RC.map s) hE hK' hF'
    (tensorResolutionChartAugmentation_quasiIso M U MA sM P) hq' hs' i

end AlgebraicGeometry
~~~

## New

~~~lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso

/-! # Affine chart comparison for tensor resolutions

Re-export the source-library construction of
`AlgebraicGeometry.tensorResolutionChartComparisonIso`. Keeping a single implementation
avoids duplicate declarations after the source-library sync. The comparison still uses the
specified chart augmentation and the four-map comparison through the restricted second
K-flat resolution.
-/

@[expose] public section
~~~

The consumer wrappers publicly import their matching source module, exposing
the original public declaration names with the canonical K-flat predicate.
The helper without a source counterpart is retained as follows:

~~~lean
/- Copyright (c) 2026 The SHEAF contributors. All rights reserved. -/
module
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionCoordinateSheafIso

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
attribute [local instance 2000] SheafOfModules.instCategory
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionCoordinateChartIso_monoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance TensorResolutionCoordinateChartIso_zero (X : Scheme.{u}) :
    (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionCoordinateChartIso_objZero (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- The comparison on the affine chart before commuting restriction and homology. -/
noncomputable def tensorResolutionCoordinateChartIso
    (Y : Scheme.{u}) (M N : Y.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (U : Y.affineOpens) (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (sN : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (P : ProjectiveResolution MA) (K F : CochainComplex Y.Modules ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj M)
    (s : F ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj N)
    (hK : CochainComplex.IsKFlatTensor (R := Y.sheaf) K)
    (hF : CochainComplex.IsKFlatTensor (R := Y.sheaf) F)
    (hq : QuasiIso q) (hs : QuasiIso s) (n : ℕ) :
    tilde (R := Γ(Y, U.1))
        ((((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj P.complex).homology n) ≅
      (CochainComplex.mapBifunctor
        (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj K)
        (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor Y.Modules 0).obj N))
        (curriedTensor (Spec Γ(Y, U.1)).Modules)).homology (-(n : ℤ)) := by
  -- The full coordinates end in inverse normalization; normalize to cancel it.
  -- This keeps the large tensor-comparison composite bundled during elaboration.
  refine tensorResolutionCoordinateSheafIso Y M N U MA NA sM sN P K F q s hK hF hq hs n ≪≫ ?_
  exact tensorResolutionNormalizedRestrictHomologyIso U.2.fromSpec K
    ((CochainComplex.singleFunctor Y.Modules 0).obj N) (-(n : ℤ))

end AlgebraicGeometry
~~~

## Users

tools/downstream.py initially reports an unknown module because the item is
quarantined; --allow-missing and a full import scan of lean/ and quarantine/
show no live Sheaf importer and the following complete archived consumer
component. All eight consumer claims were absent when checked. The archives
are preserved; none is listed in deleted.txt.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso | C1 | Restore canonical public comparison API. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIsoFormula | unclaimed | Restore module path by publicly re-exporting the complete source counterpart. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonNaturality | unclaimed | Restore module path by publicly re-exporting the complete source counterpart. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateChartIso | unclaimed | Retain the same chart helper via bundled full coordinates and normalization. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateSheafIso | unclaimed | Restore module path by publicly re-exporting the complete source counterpart. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateFactorization | unclaimed | Restore module path by publicly re-exporting the complete source counterpart. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateSections | unclaimed | Restore module path by publicly re-exporting the complete source counterpart. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateSectionsNaturality | unclaimed | Restore module path by publicly re-exporting the complete source counterpart. |
| Sheaf.AlgebraicGeometry.QCohOrdinaryTensorResolutionCoordinates | unclaimed | Restore module path by publicly re-exporting the complete source counterpart. |

The existing WeilConjectures consumers already use the canonical declaration
and are unchanged. The complete archived consumer component is delivered
together, so none keeps relying on the old predicate through these imports.

## Status

landed 20261020T162258-L-3585157 2026-10-20 (merge of deliver/C1/Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso)
