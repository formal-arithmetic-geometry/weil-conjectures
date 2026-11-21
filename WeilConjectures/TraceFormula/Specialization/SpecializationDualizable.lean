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

namespace CategoryTheory.Adjunction

variable {C D E : Type*} [Category C] [MonoidalCategory C] [Category D] [MonoidalCategory D]
  [Category E] [MonoidalCategory E] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.Monoidal]
  (I : D ⥤ E) [I.Monoidal]

/-- For an adjunction `F ⊣ G` with `F` strong monoidal and a strong monoidal functor `I`, if `I`
inverts the unit of the adjunction at `𝟙`, it inverts the unit at every dualizable object. -/
lemma isIso_map_unit_app_of_isDualizable {W : D} (hW : IsDualizable W)
    [IsIso (I.map (adj.unit.app (𝟙_ D)))] : IsIso (I.map (adj.unit.app W)) := by
  let := adj.rightAdjointLaxMonoidal
  have := adj.isIso_leftProjectionMorphism_of_isDualizable hW (F.obj (𝟙_ D))
  have : IsIso (I.map (W ◁ adj.unit.app (𝟙_ D))) := by
    rw [Functor.Monoidal.map_whiskerLeft]
    infer_instance
  have key : adj.unit.app (W ⊗ 𝟙_ D) ≫ G.map (Functor.OplaxMonoidal.δ F W (𝟙_ D)) =
      W ◁ adj.unit.app (𝟙_ D) ≫ adj.leftProjectionMorphism W (F.obj (𝟙_ D)) := by
    rw [adj.unit_app_tensor_comp_map_δ, ← adj.whiskerRight_unit_comp_homEquiv, tensorHom_def',
      Category.assoc]
    rfl
  have : IsIso (I.map (adj.unit.app (W ⊗ 𝟙_ D))) := by
    have h : IsIso (I.map (W ◁ adj.unit.app (𝟙_ D) ≫
        adj.leftProjectionMorphism W (F.obj (𝟙_ D)))) := by
      rw [I.map_comp]
      infer_instance
    rw [← key, I.map_comp] at h
    exact IsIso.of_isIso_comp_right _ (I.map (G.map (Functor.OplaxMonoidal.δ F W (𝟙_ D))))
  have h : I.map (adj.unit.app W) = I.map (ρ_ W).inv ≫ I.map (adj.unit.app (W ⊗ 𝟙_ D)) ≫
      I.map (G.map (F.map (ρ_ W).hom)) := by
    rw [← I.map_comp, ← I.map_comp]
    congr 1
    have := adj.unit.naturality (ρ_ W).hom
    simp only [Functor.id_map, Functor.comp_map] at this
    rw [← this, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

end CategoryTheory.Adjunction

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
