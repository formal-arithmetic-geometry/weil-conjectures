/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ModuleDerivedFunctorCompositorShifts
import WeilConjectures.AlgebraicGeometry.KFlatDerivedAdjunctionTransportShifts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)
/-- The prescribed projection, curried in its geometric (first) input.
It is the flipped right-adjoint projection map used by the parent devissage.
(blueprint: lem-sfb-rational-bivariate-devissage) -/
def rationalProjectionFirst
    (M : DerivedCategory (ModuleObjectRingedComparison.Internal Λ Y)) :
    moduleObjectDerivedPushforward Λ f ⋙ tensorRight M ⟶
      tensorRight ((moduleObjectDerivedPullback Λ f).obj M) ⋙ moduleObjectDerivedPushforward Λ f :=
  (derivedUpperStarLowerStarAdjunction Λ f).rightAdjointProjectionMapFlipApp
    (T_C := derivedTensor Λ X) (T_D := derivedTensor Λ Y)
    (leftDerivedUpperStarTensor Λ f) M
/-- For fixed `M`, the canonical projection `rationalProjectionFirst`, curried in the
geometric variable, commutes with the fixed integer shifts: it is `NatTrans.CommShift`
for the unsigned first-variable tensor shift and the fixed derived pushpull shifts
(def-sfb-module-derived-comparison-shifts), with the explicit component square.
Source: latest blueprint, sk-thm-sfb-proper-base-change-rational.proof.md, paragraph (3)
(det-thm-sfb-proper-base-change-rational); Stacks Project, Tags 07A4 and 0B56.

Proof: by lem-sfb-ringed-projection-first-shift the flipped right-adjoint projection
`rightAdjointProjectionMapFlipApp` commutes with shifts when `Rf_*` carries the shift
compatible with the adjunction unit and counit. By
lem-sfb-kflat-derived-adjunction-transport-shifts that shift is the fixed K-injective shift
`modulePushforwardDerivedCommShift`, and by lem-sfb-module-derived-functor-compositor-shifts
the fixed pullback shift is the one transported along the exact comparison. Hence the
projection is `NatTrans.CommShift`; the component square for each `n` is
`NatTrans.shift_app_comm`. (blueprint: lem-sfb-rational-bivariate-shift-first) -/
theorem rational_bivariate_first_shift
    (M : DerivedCategory (ModuleObjectRingedComparison.Internal Λ Y))
    : NatTrans.CommShift (rationalProjectionFirst Λ f M) ℤ ∧
      (∀ (n : ℤ) (K : DerivedCategory (ModuleObjectRingedComparison.Internal Λ X)),
        (rationalProjectionFirst Λ f M).app (K⟦n⟧) ≫
            ((tensorRight ((moduleObjectDerivedPullback Λ f).obj M) ⋙
              moduleObjectDerivedPushforward Λ f).commShiftIso n).hom.app K =
          ((moduleObjectDerivedPushforward Λ f ⋙ tensorRight M).commShiftIso n).hom.app K ≫
            (shiftFunctor _ n).map ((rationalProjectionFirst Λ f M).app K)) := by
  set_option linter.style.haveILetI false in
    letI : ∀ L, ((derivedTensor Λ Y).flip.obj L).CommShift ℤ :=
    fun L ↦ DerivedCategory.commShiftTensorRight _ L
  set_option linter.style.haveILetI false in
    letI : ∀ L, ((derivedTensor Λ X).flip.obj L).CommShift ℤ :=
    fun L ↦ DerivedCategory.commShiftTensorRight _ L
  have hadj := (kflat_derived_adjunction_transport_shifts
    (⟨Λ⟩ : Profinite.CondensedRing) f).2.2
  set_option linter.style.haveILetI false in
    letI : Adjunction.CommShift
      (F := moduleObjectDerivedPullback Λ f) (G := moduleObjectDerivedPushforward Λ f)
      (derivedUpperStarLowerStarAdjunction Λ f) ℤ := hadj
  have hcomm : NatTrans.CommShift (rationalProjectionFirst Λ f M) ℤ := by
    unfold rationalProjectionFirst
    exact CategoryTheory.Adjunction.commShift_rightAdjointProjectionMapFlipApp
      (F := moduleObjectDerivedPullback Λ f) (G := moduleObjectDerivedPushforward Λ f)
      (derivedUpperStarLowerStarAdjunction Λ f) (leftDerivedUpperStarTensor Λ f) ℤ M
  set_option linter.style.haveILetI false in
    letI := hcomm
  exact ⟨hcomm, fun n K ↦ (NatTrans.shift_app_comm _ n K).symm⟩
end AlgebraicGeometry.ProEtale.CondensedRing
