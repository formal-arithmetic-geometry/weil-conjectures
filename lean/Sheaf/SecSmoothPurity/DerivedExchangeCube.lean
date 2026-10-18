import WeilConjectures.SixFunctors.BaseChange.Derived
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option autoImplicit false

/-- The four derived exchange maps in a commutative cube satisfy the canonical
cube-pasting identity.  This is the statement corresponding to the two
possible mate pastings; the proof is supplied at a later stage.

Source: Stacks Project, `sites-cohomology.tex`, Tags 0E47 and 07A7; the
canonical-map verification in Tag 0EZT (blueprint: lem-kun-derived-exchange-cube). -/
theorem derivedExchangeCube
    {X₀ Y₀ S₀ T₀ X₁ Y₁ S₁ T₁ : Scheme.{u}}
    (h₀ : Y₀ ⟶ X₀) (e₀ : Y₀ ⟶ T₀) (f₀ : X₀ ⟶ S₀) (g₀ : T₀ ⟶ S₀)
    (h₁ : Y₁ ⟶ X₁) (e₁ : Y₁ ⟶ T₁) (f₁ : X₁ ⟶ S₁) (g₁ : T₁ ⟶ S₁)
    (h₀e₀ : h₀ ≫ f₀ = e₀ ≫ g₀) (h₁e₁ : h₁ ≫ f₁ = e₁ ≫ g₁)
    (x : X₁ ⟶ X₀) (y : Y₁ ⟶ Y₀) (s : S₁ ⟶ S₀) (a : T₁ ⟶ T₀)
    (f₀x : x ≫ f₀ = f₁ ≫ s) (g₀a : a ≫ g₀ = g₁ ≫ s)
    (h₀y : y ≫ h₀ = h₁ ≫ x) (e₀y : y ≫ e₀ = e₁ ≫ a) :
    let A := AddCommGrpCat.{u + 1}
    let E₀ := derivedBaseChangeMapPlus A (CommSq.mk h₀e₀.symm)
    let E₁ := derivedBaseChangeMapPlus A (CommSq.mk h₁e₁.symm)
    let P := derivedBaseChangeMapPlus A (CommSq.mk g₀a)
    let Q := derivedBaseChangeMapPlus A (CommSq.mk h₀y)
    let α :=
      (upperStarCompDerivedPlus A x f₀ (x ≫ f₀) rfl).symm ≪≫
        (eqToIso (by rw [f₀x])) ≪≫
          upperStarCompDerivedPlus A f₁ s (x ≫ f₀) f₀x
    let β :=
      (upperStarCompDerivedPlus A y e₀ (y ≫ e₀) rfl).symm ≪≫
        (eqToIso (by rw [e₀y])) ≪≫
          upperStarCompDerivedPlus A e₁ a (y ≫ e₀) e₀y
    Functor.whiskerLeft (lowerStar A g₀).rightDerivedFunctorPlus α.hom ≫
          Functor.whiskerRight P (upperStar A f₁).mapDerivedCategoryPlus ≫
          Functor.whiskerLeft (upperStar A a).mapDerivedCategoryPlus E₁ =
      Functor.whiskerRight E₀ (upperStar A x).mapDerivedCategoryPlus ≫
          Functor.whiskerLeft (upperStar A e₀).mapDerivedCategoryPlus Q ≫
          Functor.whiskerRight β.hom (lowerStar A h₁).rightDerivedFunctorPlus := by
  sorry

end AlgebraicGeometry.Etale
