/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalFibreCohomology
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties
import WeilConjectures.AlgebraicGeometry.HigherDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.FormalFunctionsDegreeZeroStalkIso
import WeilConjectures.AlgebraicGeometry.FormalFunctionsDegreeZeroSystemIso
import WeilConjectures.AlgebraicGeometry.FormalFunctionsDegreeZeroCompatibility

/-! # Degree-zero identifications for the formal fibre system

## References

* Stacks Project, Tags 02OD, 01E4 and 01FB
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Degree-zero derived stalks are ordinary direct-image stalks, and the degree-zero
cohomology system of the pulled-back unit module is the system of global sections.
The identifications carry the canonical stalk maps to section pullback on germs.
(Stacks, Tag 02OD; Tags 01E4 and 01FB.) -/
theorem formalFunctions_degreeZero_dictionary {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    ∃ a : ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))) ≃ₗ[
          Y.presheaf.stalk y]
        formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0,
      ∃ b : formalFibreCohomologySystem f y (SheafOfModules.unit X.ringCatSheaf) 0 ≅
          formalFibreSectionsSystem f y,
        ∀ (n : ℕ)
          (θ : formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0 →ₗ[
            Y.presheaf.stalk y]
            formalFibreCohomologyLocal f y (SheafOfModules.unit X.ringCatSheaf) 0 n),
          IsFormalFunctionsTheta f y (SheafOfModules.unit X.ringCatSheaf) 0 n θ →
          ∀ (V : Y.Opens) (hy : y ∈ V)
            (hV : (⊤ : (formalFibre f y n).Opens) ≤
              (formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)) (t : Γ(X, f ⁻¹ᵁ V)),
            (b.hom.app (op n)) (θ (a (TopCat.Presheaf.germ
              ((Scheme.Modules.pushforward f).obj
                (SheafOfModules.unit X.ringCatSheaf)).val.presheaf V y hy t))) =
              (formalFibreι f y n).appLE (f ⁻¹ᵁ V) ⊤ hV t := by
  obtain ⟨a, _, b, hb⟩ := formalFunctions_degreeZero_compatibility f y
  exact ⟨a, b, hb⟩

end AlgebraicGeometry
