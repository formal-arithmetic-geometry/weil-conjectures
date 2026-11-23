/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Specialization
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorShift
public import WeilConjectures.TraceFormula.Specialization.TraitNearbyMonoidal

/-!

# The specialization map at dualizable objects

Let `M` be a model of `X` with a projection `p : 𝒳 ⟶ X` such that `j ≫ p = ε`, and let
`σ : Lπ^* ⟶ Ψ_M` be its specialization map (`NearbyCyclesModel.specialization`). If the
specialization unit `𝟙 ⟶ Ψ_M 𝟙` is an isomorphism, then `σ(K)` is an isomorphism for every
dualizable `K` (`NearbyCyclesModel.isIso_specialization_app_of_isDualizable`).

Indeed `σ(K)` is `Li^*` of the unit of `Lj^* ⊣ Rj_*` at the dualizable object `Lp^* K`, and a
monoidal functor which inverts the unit at `𝟙` inverts it at every dualizable object
(`CategoryTheory.Adjunction.isIso_map_unit_app_of_isDualizable`): up to the tensor structure of
the left adjoint `F`, the unit at `W ⊗ 𝟙` is `W ◁ η_𝟙` followed by the left projection morphism
`W ⊗ G F 𝟙 ⟶ G (F W ⊗ F 𝟙)`, which is invertible for dualizable `W`.

The file also shows that the specialization map commutes with the shifts
(`NearbyCyclesModel.commShift_specialization`).

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} (M : NearbyCyclesModel X X') (p : M.total ⟶ X) (hp : M.j ≫ p = M.ε)
  {π : X' ⟶ X} (hπ : M.i ≫ p = π)

/-- **The specialization map at dualizable objects**: if the specialization unit
`𝟙 ⟶ Ψ_M 𝟙` of a model `M` is an isomorphism, then so is the specialization map
`σ(K) : Lπ^* K ⟶ Ψ_M K` at every dualizable `K`. -/
theorem isIso_specialization_app_of_isDualizable [IsIso (M.unit Λ)]
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))} (hK : IsDualizable K) :
    IsIso ((M.specialization Λ p hp hπ).app K) := by
  have hu : IsIso (M.unit Λ) := inferInstance
  rw [unit] at hu
  have := @IsIso.of_isIso_comp_left _ _ _ _ _ (leftDerivedUpperStarUnitIso Λ M.i).inv _ _ hu
  rw [Functor.map_comp] at this
  have : IsIso (L((M.i)^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ M.j).unit.app (𝟙_ _))) :=
    IsIso.of_isIso_comp_right _ (L((M.i)^*⟦Λ⟧).map (R((M.j)_*⟦Λ⟧).map
      ((leftDerivedUpperStarUnitIso Λ M.j).hom ≫ (leftDerivedUpperStarUnitIso Λ M.ε).inv)))
  have hW : IsDualizable (L((p)^*⟦Λ⟧).obj K) := by
    obtain ⟨_⟩ := hK
    exact ⟨@HasRightDual.mk _ _ _ _ _ (ExactPairing.map L((p)^*⟦Λ⟧) K Kᘁ)⟩
  have := (derivedUpperStarLowerStarAdjunction Λ M.j).isIso_map_unit_app_of_isDualizable
    L((M.i)^*⟦Λ⟧) hW
  rw [specialization_app, Functor.map_comp]
  infer_instance

instance {B₀ B₁ B₂ : Scheme.{u}} {a : B₀ ⟶ B₁} {b : B₁ ⟶ B₂} {ab : B₀ ⟶ B₂} (h : a ≫ b = ab) :
    NatTrans.CommShift (leftDerivedUpperStarCompOfEq Λ h).hom ℤ := by
  subst h
  exact inferInstanceAs (NatTrans.CommShift (leftDerivedUpperStarComp Λ a b).hom ℤ)

instance {B₀ B₁ B₂ : Scheme.{u}} {a : B₀ ⟶ B₁} {b : B₁ ⟶ B₂} {ab : B₀ ⟶ B₂} (h : a ≫ b = ab) :
    NatTrans.CommShift (leftDerivedUpperStarCompOfEq Λ h).inv ℤ := by
  subst h
  exact inferInstanceAs (NatTrans.CommShift (leftDerivedUpperStarComp Λ a b).inv ℤ)

/-- The specialization map `σ : Lπ^* ⟶ Ψ_M` commutes with the shifts. -/
instance commShift_specialization :
    NatTrans.CommShift (M.specialization Λ p hp hπ) ℤ := by
  have e : M.specialization Λ p hp hπ = (leftDerivedUpperStarCompOfEq Λ hπ).hom ≫
      L((p)^*⟦Λ⟧).whiskerLeft L((M.i)^*⟦Λ⟧).leftUnitor.inv ≫
      L((p)^*⟦Λ⟧).whiskerLeft (Functor.whiskerRight
        (derivedUpperStarLowerStarAdjunction Λ M.j).unit L((M.i)^*⟦Λ⟧)) ≫
      L((p)^*⟦Λ⟧).whiskerLeft (Functor.associator L((M.j)^*⟦Λ⟧) R((M.j)_*⟦Λ⟧)
        L((M.i)^*⟦Λ⟧)).hom ≫
      (Functor.associator L((p)^*⟦Λ⟧) L((M.j)^*⟦Λ⟧) (R((M.j)_*⟦Λ⟧) ⋙ L((M.i)^*⟦Λ⟧))).inv ≫
      Functor.whiskerRight (leftDerivedUpperStarCompOfEq Λ hp).inv
        (R((M.j)_*⟦Λ⟧) ⋙ L((M.i)^*⟦Λ⟧)) := by
    ext K
    simp [specialization]
  rw [e]
  infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
