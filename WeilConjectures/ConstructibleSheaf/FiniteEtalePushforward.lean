/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.DisjointUnion
public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyTrivial

/-!
# Pushforwards of constant sheaves along finite étale morphisms

For a finite étale morphism `π : V ⟶ X`, the pushforward `π_* M_V` of a constant sheaf is
locally constant (`AlgebraicGeometry.Scheme.isLocallyConstantSheaf_lowerStar_constantSheaf`):
étale locally `π` is a trivial cover `∐ₛ U ⟶ U`
(`AlgebraicGeometry.Scheme.FiniteEtale.exists_etale_isPullback_sigma`), the pushforward commutes
with this base change (`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite`), and along a
trivial cover the pushforward of a constant sheaf is constant
(`AlgebraicGeometry.Scheme.isConstant_lowerStar_trivialCoverFold`). This is an input to the
constructibility of extensions by zero along étale maps [Stacks 03SA].
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {V X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

/-- **The pushforward of a constant sheaf along a finite étale morphism is locally constant**:
étale locally the morphism is a trivial cover `∐ₛ U ⟶ U`, the pushforward commutes with this
base change (finite base change), and along a trivial cover the pushforward of a constant sheaf
is constant. -/
theorem isLocallyConstantSheaf_lowerStar_constantSheaf (π : V ⟶ X) [IsFinite π] [Etale π]
    (M : ModuleCat.{u + 1} Λ) :
    IsLocallyConstantSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) π).obj
      ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  let P : X.FiniteEtale := ⟨MorphismProperty.Over.mk ⊤ π inferInstance,
    (inferInstance : IsFinite π)⟩
  choose U g hg S hS fst hx hpb using fun x ↦ FiniteEtale.exists_etale_isPullback_sigma P x
  let 𝒰 : Cover.{u} etalePrecoverage X :=
    { I₀ := X
      X := U
      f := g
      mem₀ := (presieve₀_mem_precoverage_iff _).mpr ⟨fun x ↦ by
        obtain ⟨y, hy⟩ := hx x
        exact ⟨x, y, hy⟩, fun x ↦ hg x⟩ }
  refine ⟨⟨𝒰, fun x ↦ ?_⟩⟩
  rw [isConstant_over_iff_upperStar]
  change ((Etale.upperStar _ (g x)).obj _).IsConstant _
  have : IsFinite P.obj.hom := (inferInstance : IsFinite π)
  have := Etale.isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} Λ) (hpb x)
  have : (((Etale.lowerStar (ModuleCat.{u + 1} Λ) (trivialCoverFold (U x) (S x))).obj
      ((constantSheaf _ (ModuleCat.{u + 1} Λ)).obj M))).IsConstant (U x).smallEtaleTopology :=
    isConstant_lowerStar_trivialCoverFold M
  exact Sheaf.isConstant_congr _
    ((Etale.lowerStar _ (trivialCoverFold (U x) (S x))).mapIso
      ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) (fst x)).app M).symm ≪≫
      (asIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) (hpb x).toCommSq).app _)).symm)

end AlgebraicGeometry.Scheme
