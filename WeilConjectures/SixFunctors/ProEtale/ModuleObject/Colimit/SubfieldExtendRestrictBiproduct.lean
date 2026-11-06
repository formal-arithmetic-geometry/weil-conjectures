/-- If `F_X` is finite free of rank `d` over `E_X`, the derived extension of scalars along
`E_X ⟶ F_X` followed by the restriction of scalars is the biproduct power `K ↦ Kᵈ`. -/
noncomputable def extendScalarsCompRestrictScalarsIsoBiproductPow (X : Scheme.{u}) {d : ℕ}
    (e : (Mod.comap (padicSubfieldRingObjMap X ℓ h)).obj
        (Mod.regular (padicSubfieldRingObj X ℓ F)) ≅
      Mod.finiteFree (padicSubfieldRingObj X ℓ E) d) :
    L(Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)) ⋙
        D(Mod.comap (padicSubfieldRingObjMap X ℓ h)) ≅
      Functor.finBiproductPow _ d := by
  have e' := Mod.extendScalarsCompComapIsoBiproductPow _ e
  have := Functor.additive_biproductPow
    (A := Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) d
  have := preservesFiniteLimits_of_natIso e'
  have := preservesFiniteColimits_of_natIso e'
  exact Functor.isoWhiskerRight
      (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).leftDerivedFunctorIsoMapDerivedCategory
      _ ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫ Functor.mapDerivedCategoryNatIso e' ≪≫
    Functor.mapDerivedCategoryBiproductPowIso _ d

/-- Blueprint `sk-prop-sfb-cartesian-coefficients`: for finite subextensions `E ≤ F`, the
derived extension of scalars along `E_X ⟶ F_X` followed by the restriction of scalars is the
biproduct power `K ↦ Kᵈ` on the unbounded derived category of `E_X`-modules, for a rank `d`
independent of the scheme `X`. -/
theorem exists_extendScalars_comp_restrictScalars_iso_biproductPow :
    ∃ d : ℕ, ∀ X : Scheme.{u},
      Nonempty (L(Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)) ⋙
          D(Mod.comap (padicSubfieldRingObjMap X ℓ h)) ≅
        Functor.finBiproductPow _ d) := by
  obtain ⟨d, hd⟩ := exists_comap_regular_iso_finiteFree.{u} ℓ h
  exact ⟨d, fun X ↦ (hd X).map (extendScalarsCompRestrictScalarsIsoBiproductPow ℓ h X)⟩

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryBiproductPow
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsComapBiproduct
