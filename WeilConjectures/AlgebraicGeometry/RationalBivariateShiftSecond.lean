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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.AlgebraicGeometry.KFlatDerivedAdjunctionTransportShifts
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)
/-- The prescribed projection, curried in its scalar (second) input.
It is the right-adjoint projection map used by the parent devissage.
(blueprint: lem-sfb-rational-bivariate-devissage) -/
def rationalProjectionSecond
    (K : DerivedCategory (ModuleObjectRingedComparison.Internal Λ X)) :
    tensorLeft ((moduleObjectDerivedPushforward Λ f).obj K) ⟶
      moduleObjectDerivedPullback Λ f ⋙ tensorLeft K ⋙ moduleObjectDerivedPushforward Λ f :=
  ((derivedUpperStarLowerStarAdjunction Λ f).rightAdjointProjectionMap
    (T_C := derivedTensor Λ X) (T_D := derivedTensor Λ Y)
    (leftDerivedUpperStarTensor Λ f)).app K
/-- For fixed `K`, the canonical projection `rationalProjectionSecond`, curried in the
scalar variable, commutes with the fixed integer shifts: it is `NatTrans.CommShift` for
the signed second-variable tensor shift and the fixed derived pushpull shifts
(def-sfb-module-derived-comparison-shifts), with the explicit component square.
Source: latest blueprint, sk-thm-sfb-proper-base-change-rational.proof.md, paragraph (3)
(det-thm-sfb-proper-base-change-rational); Stacks Project, Tags 07A4 and 0B56.

Proof: `kflat_derived_adjunction_transport_shifts` makes the specified derived adjunction
compatible with the fixed module pullback and pushforward shifts. Apply the generic
`Adjunction.commShift_rightAdjointProjectionMap_app` to this adjunction, using the native
tensor-comparison and tensor-map shift instances. Compose with the shift-compatible
functor associator to recover the right-associated target of `rationalProjectionSecond`.
Its components are identities, so this composite is the prescribed map. The explicit
component square is `NatTrans.shift_app_comm`, with its equality reversed.
(blueprint: lem-sfb-rational-bivariate-shift-second) -/
theorem rational_bivariate_second_shift
    (K : DerivedCategory (ModuleObjectRingedComparison.Internal Λ X))
    : NatTrans.CommShift (rationalProjectionSecond Λ f K) ℤ ∧
      (∀ (n : ℤ) (M : DerivedCategory (ModuleObjectRingedComparison.Internal Λ Y)),
        (rationalProjectionSecond Λ f K).app (M⟦n⟧) ≫
            ((moduleObjectDerivedPullback Λ f ⋙ tensorLeft K ⋙
              moduleObjectDerivedPushforward Λ f).commShiftIso n).hom.app M =
          ((tensorLeft ((moduleObjectDerivedPushforward Λ f).obj K)).commShiftIso n).hom.app
              M ≫ (shiftFunctor _ n).map ((rationalProjectionSecond Λ f K).app M)) := by
  have hadj : Adjunction.CommShift
      (F := moduleObjectDerivedPullback Λ f)
      (G := moduleObjectDerivedPushforward Λ f)
      (derivedUpperStarLowerStarAdjunction Λ f) ℤ :=
    (kflat_derived_adjunction_transport_shifts (Mon.mk Λ) f).2.2
  let π : tensorLeft ((moduleObjectDerivedPushforward Λ f).obj K) ⟶
      ((moduleObjectDerivedPullback Λ f ⋙ tensorLeft K) ⋙
        moduleObjectDerivedPushforward Λ f) :=
    ((derivedUpperStarLowerStarAdjunction Λ f).rightAdjointProjectionMap
      (T_C := derivedTensor Λ X) (T_D := derivedTensor Λ Y)
      (leftDerivedUpperStarTensor Λ f)).app K
  have hπ : NatTrans.CommShift π ℤ :=
    Adjunction.commShift_rightAdjointProjectionMap_app
      (F := moduleObjectDerivedPullback Λ f) (G := moduleObjectDerivedPushforward Λ f)
      (derivedUpperStarLowerStarAdjunction Λ f) (leftDerivedUpperStarTensor Λ f) K
  have heq : rationalProjectionSecond Λ f K = π ≫
      (Functor.associator (moduleObjectDerivedPullback Λ f) (tensorLeft K)
        (moduleObjectDerivedPushforward Λ f)).hom := by
    ext M
    simp [rationalProjectionSecond, π]
  have hcomm : NatTrans.CommShift (rationalProjectionSecond Λ f K) ℤ := by
    rw [heq]
    infer_instance
  refine ⟨hcomm, ?_⟩
  intro n M
  exact (NatTrans.shift_app_comm (rationalProjectionSecond Λ f K) n M).symm
end AlgebraicGeometry.ProEtale.CondensedRing
