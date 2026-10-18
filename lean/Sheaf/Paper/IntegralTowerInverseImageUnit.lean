/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# The tensor-unit comparison on whole quotient towers

Source: Stacks Project, Tags 03D6 and 0941; blueprint Global powers in
`sec-trace-formula/sk-thm-trace-transport/thm-trf-l-function-euler-product.proof.md`
(blueprint: def-trf-integral-tower-inverse-image-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

/-- Apply the specified exact completed inverse image to every level and transition.
Source: Stacks 03D6, 0941 (blueprint: def-trf-integral-tower-inverse-image-unit). -/
abbrev integralTowerInverseImage :
    (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤ (ℕᵒᵖ ⥤ scalarReductionSource l E X) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (inverseImageIntegralModules l E g)

/-- Levelwise finite-limit preservation by the exact inverse image.
Source: Stacks 0941 (blueprint: def-trf-integral-tower-inverse-image-unit). -/
instance integralTowerInverseImageLimits : PreservesFiniteLimits
    (integralTowerInverseImage l E g) := ⟨fun _ _ _ ↦ inferInstance⟩

/-- Levelwise finite-colimit preservation by the exact inverse image.
Source: Stacks 0941 (blueprint: def-trf-integral-tower-inverse-image-unit). -/
instance integralTowerInverseImageColimits : PreservesFiniteColimits
    (integralTowerInverseImage l E g) := ⟨fun _ _ _ ↦ inferInstance⟩

/-- The whole-tower unit is uniquely determined by the sheafified tensor unit at
all indices and all sections. Source: Stacks 03D6, 0941
(blueprint: def-trf-integral-tower-inverse-image-unit).

Proof: evaluate the actual sequence-pullback adjunction unit at the postcomposition
of U with g, then restrict along the distinguished comma arrow U to g-star(gU).
This sends x to x tensor 1. The completed coefficient projection equation proves
linearity after restriction of scalars. Naturality in restrictions and quotient
transitions gives a map of entire towers, natural in the quotient system.
The coefficient map is invertible and the underlying site map is an equivalence,
so multiplication gives its inverse at each level. Sectionwise equality proves
uniqueness of the transformation and its inverse. -/
theorem integralTowerInverseImageUnit_existsUnique :
    ∃! a : coefficientSequenceRestriction l E Y ⋙ integralTowerInverseImage l E g ≅
        integralComparisonSequencePullback l E g ⋙ coefficientSequenceRestriction l E X,
      ∀ (M : coefficientSequenceModules l E Y) (n : ℕ) (U : X.ProEt)
        (x : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U))),
        ((a.hom.app M).app (op n)).val.app (op U)
            (integralComparisonRestrictedSection l E Y M n
              (op ((proEtaleIsoPostcompose g).obj U)) x) =
          integralComparisonRestrictedSection l E X
            ((integralComparisonSequencePullback l E g).obj M) n (op U)
            (((integralComparisonSequencePullback l E g).obj M).val.map
              (CategoryTheory.Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
              (integralComparisonSequenceGenerator l E g M n
                ((proEtaleIsoPostcompose g).obj U) x)) := by
  sorry

/-- The canonical sheafified x tensor 1 map, retaining all quotient transitions.
Source: Stacks 03D6, 0941 (blueprint: def-trf-integral-tower-inverse-image-unit). -/
def integralTowerInverseImageUnit :=
  (integralTowerInverseImageUnit_existsUnique l E g).exists.choose

/-- Exact inverse image of the entire completed-coefficient tower.
Source: Stacks 03D6, 0941 (blueprint: def-trf-integral-tower-inverse-image-unit). -/
def integralDerivedTowerInverseImage :
    coefficientSequenceRestrictedDerived l E Y ⥤ coefficientSequenceRestrictedDerived l E X :=
  (integralTowerInverseImage l E g).mapDerivedCategory

/-- Localize the same whole-tower tensor-unit map, including the canonical
composition comparisons of exact derived functors.
Source: Stacks 03D6, 0941 (blueprint: def-trf-integral-tower-inverse-image-unit). -/
def integralDerivedTowerInverseImageUnit :
    coefficientSequenceDerivedRestriction l E Y ⋙ integralDerivedTowerInverseImage l E g ≅
      integralComparisonDerivedSequencePullback l E g ⋙
        coefficientSequenceDerivedRestriction l E X :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (integralTowerInverseImageUnit l E g) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Exact inverse image commutes with the diagonal by the identity at each level.
Source: Stacks 0941 (blueprint: def-trf-integral-tower-inverse-image-unit). -/
def integralTowerInverseImageDiagonal :
    inverseImageIntegralDerived l E g ⋙ integralComparisonConstantTower l E X ≅
      integralComparisonConstantTower l E Y ⋙ integralDerivedTowerInverseImage l E g :=
  (Functor.mapDerivedCategoryCompIso
    (inverseImageIntegralModules l E g)
    (Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤ _)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (@id
        (inverseImageIntegralModules l E g ⋙
            (Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤ _) ≅
          (Functor.const ℕᵒᵖ : scalarReductionSource l E Y ⥤ _) ⋙
            integralTowerInverseImage l E g)
        (Functor.compConstIso ℕᵒᵖ (inverseImageIntegralModules l E g))) ≪≫
      Functor.mapDerivedCategoryCompIso
        (Functor.const ℕᵒᵖ : scalarReductionSource l E Y ⥤ _)
        (integralTowerInverseImage l E g)

end WeilConjectures
