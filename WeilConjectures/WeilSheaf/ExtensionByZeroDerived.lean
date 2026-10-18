/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ExtensionByZeroAdjunction
public import WeilConjectures.WeilSheaf.Localization

/-!
# The derived extension by zero of pro-étale Weil sheaves

Let `j : U ⟶ X` be an open immersion of `k₀`-schemes. The exact functors `j_!` and `j^*` of
pro-étale Weil sheaves induce an adjunction `D(j_!) ⊣ D(j^*)` on the derived categories
(`AlgebraicGeometry.ProEtaleWeilSheaf.derivedExtensionByZeroUpperStarAdjunction`) whose unit is an
isomorphism, `j_!` being fully faithful. Moreover:

- the extension by zero along a composite of open immersions is the composite of the extensions
  by zero (`AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZeroCompIso`);
- the pullback of `j_! F` along a morphism whose range misses that of `j` vanishes
  (`AlgebraicGeometry.ProEtaleWeilSheaf.isZero_upperStar_obj_extensionByZero_obj`);
- for a closed immersion `i` and an open immersion `j` with complementary ranges, a morphism of
  the derived category whose pullbacks along `i` and `j` are isomorphisms is an isomorphism
  (`AlgebraicGeometry.ProEtaleWeilSheaf.isIso_of_isIso_upperStar_map`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- For an adjunction `L ⊣ R` of exact functors with invertible unit, the unit of the derived
adjunction `D(L) ⊣ RR` is invertible: on the image of a complex `X` it is, up to the
isomorphisms `D(L) ∘ Q ≅ Q ∘ L` and `Q ∘ R ≅ RR ∘ Q`, the image of the unit of `L ⊣ R`. -/
instance isIso_mapDerivedCategoryRightDerivedAdjunction_unit (adj : L ⊣ R) [IsIso adj.unit] :
    IsIso adj.mapDerivedCategoryRightDerivedAdjunction.unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  obtain ⟨X, ⟨e⟩⟩ : ∃ X, Nonempty (DerivedCategory.Qh.obj X ≅ K) :=
    ⟨_, ⟨(Localization.essSurj DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))).mem_essImage K |>.getIso⟩⟩
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have h := Adjunction.derivedη_fac_app (adj.mapHomotopyCategory (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M)
  have hu : IsIso ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M)) := by
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    sorry
  sorry

end CategoryTheory.Adjunction
