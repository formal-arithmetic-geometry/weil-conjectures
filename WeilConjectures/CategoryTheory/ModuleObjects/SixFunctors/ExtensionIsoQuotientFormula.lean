/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

/-! # The quotient formula for extension along an invertible scalar morphism
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

/-- The adjoint-uniqueness comparison for extension along an invertible scalar morphism
is the unique factor of the inverse scalar action through the defining coequalizer.
Its inverse inserts the unit, both maps are linear and inverse, and both are natural. -/
theorem extensionIso_quotient_formula
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] [HasEqualizers C] [HasCoequalizers C]
    [∀ X : C, PreservesColimits (tensorLeft X)]
    [∀ X : C, PreservesColimits (tensorRight X)]
    {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ] (N : Mod C R) :
    ((S ◁ φ ≫ μ[S]) ▷ N.X) ≫ (asIso φ).inv ▷ N.X ≫ γ[R,N.X] =
      ((α_ S R N.X).hom ≫ S ◁ γ[R,N.X]) ≫ (asIso φ).inv ▷ N.X ≫ γ[R,N.X] ∧
    @extendπ C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N ≫ ((@extendScalarsIsoComapInv C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ _).hom.app N).hom =
      (asIso φ).inv ▷ N.X ≫ γ[R,N.X] ∧
    (∀ f : (@extendScalarsObj C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N).X ⟶ N.X,
      @extendπ C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N ≫ f = (asIso φ).inv ▷ N.X ≫ γ[R,N.X] →
        f = ((@extendScalarsIsoComapInv C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ _).hom.app N).hom) ∧
    ((@extendScalarsIsoComapInv C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ _).inv.app N).hom =
      (λ_ N.X).inv ≫ η[S] ▷ N.X ≫ @extendπ C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N ∧
    γ[S,(@extendScalarsObj C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N).X] ≫ ((@extendScalarsIsoComapInv C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ _).hom.app N).hom =
      S ◁ ((@extendScalarsIsoComapInv C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ _).hom.app N).hom ≫
        (asIso φ).inv ▷ N.X ≫ γ[R,N.X] ∧
    ((asIso φ).inv ▷ N.X ≫ γ[R,N.X]) ≫
        (λ_ N.X).inv ≫ η[S] ▷ N.X ≫ @extendπ C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N =
      S ◁ ((λ_ N.X).inv ≫ η[S] ▷ N.X ≫ @extendπ C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N) ≫
        γ[S,(@extendScalarsObj C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N).X] ∧
    ((λ_ N.X).inv ≫ η[S] ▷ N.X ≫ @extendπ C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N) ≫
        ((@extendScalarsIsoComapInv C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ _).hom.app N).hom = 𝟙 N.X ∧
    ((@extendScalarsIsoComapInv C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ _).hom.app N).hom ≫
        (λ_ N.X).inv ≫ η[S] ▷ N.X ≫ @extendπ C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N = 𝟙 (@extendScalarsObj C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N).X ∧
    (∀ (N' : Mod C R) (h : N ⟶ N'),
      ((@extendScalars C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _).map h).hom ≫ ((@extendScalarsIsoComapInv C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ _).hom.app N').hom =
          ((@extendScalarsIsoComapInv C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ _).hom.app N).hom ≫ h.hom ∧
      h.hom ≫ (λ_ N'.X).inv ≫ η[S] ▷ N'.X ≫ @extendπ C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N' =
        ((λ_ N.X).inv ≫ η[S] ▷ N.X ≫ @extendπ C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _ N) ≫ ((@extendScalars C _ _ _
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X))
        (fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X))
        _ R S _ _ _ φ _).map h).hom) := by
  let : ∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
    fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorLeft X)
  let : ∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
    fun X ↦ preservesSmallestColimits_of_preservesColimits (tensorRight X)
  let e : extendScalars φ ≅ comap (asIso φ).inv := extendScalarsIsoComapInv φ
  -- The comparison carries the extension unit to the identity inverse-restriction unit.
  have hunit (M : Mod C R) : extendUnitHom φ M ≫ (e.hom.app M).hom = 𝟙 M.X := by
    have h := congrArg Hom.hom
      (Adjunction.homEquiv_leftAdjointUniq_hom_app
        (extendRestrictAdjunction φ) (comapEquivalenceOfIsIso φ).symm.toAdjunction M)
    rw [extendRestrictAdjunction, Adjunction.mkOfHomEquiv_homEquiv] at h
    change extendUnitHom φ M ≫ (e.hom.app M).hom = _ at h
    have hid : ((comapEquivalenceOfIsIso φ).symm.toAdjunction.unit.app M).hom =
        𝟙 M.X := by
      change (𝟙 M.X ≫ 𝟙 M.X) ≫ 𝟙 M.X = 𝟙 M.X
      simp only [Category.id_comp]
    exact h.trans hid
  have hinv (M : Mod C R) : (e.inv.app M).hom = extendUnitHom φ M := by
    apply (cancel_mono (e.hom.app M).hom).1
    rw [hunit]
    exact congrArg Hom.hom (e.inv_hom_id_app M)
  -- Linearity turns the unit equation into the formula on the coequalizer projection.
  have hlinear : γ[S,(extendScalarsObj φ N).X] ≫ (e.hom.app N).hom =
      S ◁ (e.hom.app N).hom ≫ (asIso φ).inv ▷ N.X ≫ γ[R,N.X] :=
    act_hom (e.hom.app N)
  have hquot : extendπ φ N ≫ (e.hom.app N).hom =
      (asIso φ).inv ▷ N.X ≫ γ[R,N.X] := by
    rw [← whiskerLeft_extendUnitHom_smul' φ N, Category.assoc, hlinear,
      ← whiskerLeft_comp_assoc, hunit, whiskerLeft_id, Category.id_comp]
  refine ⟨?_, hquot, ?_, hinv N, hlinear, ?_, ?_, ?_, ?_⟩
  · rw [← hquot]
    simpa only [Category.assoc] using
      congrArg (fun f ↦ f ≫ (e.hom.app N).hom) (extendπ_condition φ N)
  · intro f hf
    exact (cancel_epi (extendπ φ N)).1 (hf.trans hquot.symm)
  · change ((asIso φ).inv ▷ N.X ≫ γ[R,N.X]) ≫ extendUnitHom φ N =
      S ◁ extendUnitHom φ N ≫ γ[S,(extendScalarsObj φ N).X]
    rw [← hinv]
    exact act_hom (e.inv.app N)
  · exact hunit N
  · change (e.hom.app N).hom ≫ extendUnitHom φ N = _
    rw [← hinv]
    exact congrArg Hom.hom (e.hom_inv_id_app N)
  · intro N' h
    constructor
    · exact congrArg Hom.hom (e.hom.naturality h)
    · change h.hom ≫ extendUnitHom φ N' =
        extendUnitHom φ N ≫ ((extendScalars φ).map h).hom
      have h' := congrArg Hom.hom (e.inv.naturality h)
      change h.hom ≫ (e.inv.app N').hom =
        (e.inv.app N).hom ≫ ((extendScalars φ).map h).hom at h'
      simpa only [hinv] using h'

end CategoryTheory.Mod
