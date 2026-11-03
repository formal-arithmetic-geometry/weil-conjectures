/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.InternalBar.CondensedInternalBarResolution
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
import WeilConjectures.AlgebraicGeometry.ProfiniteFreeSlice.ProfiniteFreeSlicePointCancellation

/-! # The point-module compositor over the profinite projection

Source: HRS Section 3; Stacks Tag 03D8.
(blueprint: new-c1-profinite-free-slice-point-composition).

The point compositor is lifted from the abelian compositor using scalar
restriction along the coefficient isomorphism. Its underlying-map equation
records the prescribed abelian comparison, which is used by the parent record.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ProfiniteFreeSlice

private theorem point_cancel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (P : Profinite.{u}) :
    ∃ e : (pointModulePullback Λ X ⋙
        (upperStar Ab.{u + 1} (test X P).hom).mapMod (condensedRingObj Λ X)) ⋙
        Mod.extendScalars (condensedPullbackHom Λ (test X P).hom) ≅
      pointModulePullback Λ (test X P).left,
      ∀ M, (e.hom.app M).hom =
        ((Mod.extendScalarsIsoComapInv
          (condensedPullbackHom Λ (test X P).hom)).hom.app
          ((pointModulePullback Λ X ⋙
            (upperStar Ab.{u + 1} (test X P).hom).mapMod
              (condensedRingObj Λ X)).obj M)).hom ≫
          ((Functor.mapModCompIso (upperStarFromPoint X)
            (upperStar Ab.{u + 1} (test X P).hom)
            (upperStarFromPointComp (test X P).hom).hom Λ).hom.app M).hom := by
  exact profiniteFreeSlice_exists_cancel (condensedPullbackHom Λ (test X P).hom)
    (pointModulePullback Λ X ⋙
      (upperStar Ab.{u + 1} (test X P).hom).mapMod (condensedRingObj Λ X))
    (pointModulePullback Λ (test X P).left)
    (Functor.mapModCompIso (upperStarFromPoint X)
      (upperStar Ab.{u + 1} (test X P).hom)
      (upperStarFromPointComp (test X P).hom).hom Λ)

set_option maxHeartbeats 1600000 in
-- The scalar-extension compositor needs extra elaboration through module actions.
/-- The module compositor with the prescribed underlying abelian comparison.
Source: HRS Section 3; Stacks Tag 03D8
(blueprint: new-c1-profinite-free-slice-point-composition).
Proof: lift the monoidal abelian compositor by `mapModCompIso`, then cancel the
coefficient restriction with extension along the coefficient isomorphism.
Forgetting the action, the restriction equivalence has identity unit; the only
remaining maps are the scalar-extension forgetful comparison followed by the
original abelian compositor. -/
theorem exists_point_comparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (P : Profinite.{u}) :
    ∃ c : pointModulePullback Λ X ⋙ restriction Λ X P ≅
      pointModulePullback Λ (test X P).left,
      ∀ M : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
        (c.hom.app M).hom =
          (profinitePointModuleForgetPullbackIso Λ (test X P).hom).hom.app
              ((pointModulePullback Λ X).obj M) ≫
            (upperStarFromPointComp (test X P).hom).hom.app M.X := by
  let f := (test X P).hom
  let m := Functor.mapModCompIso (upperStarFromPoint X) (upperStar Ab.{u + 1} f)
    (upperStarFromPointComp f).hom Λ
  obtain ⟨e, he⟩ := point_cancel Λ X P
  refine ⟨(Functor.associator _ _ _).symm ≪≫ e, ?_⟩
  intro M
  simp only [Iso.trans_hom, NatTrans.comp_app, Mod.comp_hom']
  erw [Category.id_comp]
  change (e.hom.app M).hom =
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).hom.app
      ((pointModulePullback Λ X ⋙
        (upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ X)).obj M)).hom ≫
      (upperStarFromPointComp f).hom.app M.X
  simpa only [m, Functor.mapModCompIso_hom_app_hom] using he M

end AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
