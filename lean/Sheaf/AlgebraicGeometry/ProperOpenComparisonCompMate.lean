/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProperOpenComparison
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! The mate calculation used in the composition law for proper-open comparisons.

Source: the composition calculation in blueprint
`lem-weil-pbc-proper-open-comparison-composition`, steps 3--5.
(blueprint: lem-weil-pbc-proper-open-comparison-composition-mate).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The two candidate composites have the same mate under the derived open adjunction.
The composition isomorphism is required to be the canonical right-derived composition
isomorphism. The proof computes the restriction maps on a bounded-below injective
representative; the fibre-product associator gives the composite restriction, and the
clopen-section calculation identifies each restriction with the corresponding
`properOpenIdentification`. Naturality of these
restriction maps at the comparison morphisms gives the displayed mate equality.
(blueprint: lem-weil-pbc-proper-open-comparison-composition-mate)
-/
theorem properOpenComparison_comp_mate (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T₁ T₂ T₃ X : Scheme.{u}} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃)
    [IsProper f] [IsProper g]
    [((lowerStar (ModuleCat.{u + 1} Λ) f)).PreservesInjectiveObjects]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (j₃ : X ⟶ T₃)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j₃]
    (hf : j₁ ≫ f = j₂) (hg : j₂ ≫ g = j₃)
    (c : rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f ⋙
        rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) g ≅
      rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) (f ≫ g))
    (hc : c = Functor.rightDerivedFunctorPlusCompIso'
      (lowerStar (ModuleCat.{u + 1} Λ) f)
      (lowerStar (ModuleCat.{u + 1} Λ) g)
      (lowerStarComp (ModuleCat.{u + 1} Λ) f g))
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    let a := derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
      (ModuleCat.{u + 1} Λ) j₃
    a.homEquiv _ _
        (properOpenComparison Λ (f ≫ g) j₁ j₃
          ((Category.assoc j₁ f g).symm.trans ((congrArg (· ≫ g) hf).trans hg)) K ≫
          c.inv.app
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj
              K)) =
      a.homEquiv _ _
        (properOpenComparison Λ g j₂ j₃ hg K ≫
          (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) g).map
            (properOpenComparison Λ f j₁ j₂ hf K)) := by
  sorry

end AlgebraicGeometry.Etale
