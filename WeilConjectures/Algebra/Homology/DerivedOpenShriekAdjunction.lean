/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
public import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# Derived extension-by-zero and restriction adjunction

## References

* Stacks Project, Tag 08BT (used in Tag 08BW), Tags 015F and 09T5
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u w

namespace AlgebraicGeometry

/-- For an open subspace `U` of a ringed space `X`, the exact functors extension by zero
`j_! = extensionByZeroPresheaf ⋙ sheafification` and restriction
`j⁻¹ = SheafOfModules.overFunctor (moduleRings X) U`, applied termwise to complexes, induce
functors `Functor.mapDerivedCategory` on the unbounded derived categories, and these are
adjoint: `j_! ⊣ j⁻¹` on `D(O_U)` and `D(O_X)`.
The `homEquiv` is the natural bijection `Hom_{D(O_X)}(j_! A, B) ≃ Hom_{D(O_U)}(A, B|_U)`. -/
theorem derived_open_shriek_adjunction (X : RingedSpace.{u}) (U : Opens X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over U))] :
    Nonempty
      (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
          (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
            PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj))
          (Adjunction.left_adjoint_additive
            (Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2))
          (open_restriction_adjunction_exact X U).2.2.1
          (open_restriction_adjunction_exact X U).2.2.2.1 ⊣
        (SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory) := by
  let G := SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) U ⋙
    PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)
  let F := SheafOfModules.overFunctor.{u} (moduleRings X) U
  let adj : G ⊣ F := Classical.choice (open_restriction_adjunction_exact X U).2.2.2.2
  have : G.Additive := adj.left_adjoint_additive
  have : PreservesFiniteLimits G := (open_restriction_adjunction_exact X U).2.2.1
  have : PreservesFiniteColimits G := (open_restriction_adjunction_exact X U).2.2.2.1
  let : CatCommSq (G.mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh DerivedCategory.Qh G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactorsh.symm⟩
  let : CatCommSq (F.mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh DerivedCategory.Qh F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactorsh.symm⟩
  exact ⟨(adj.mapHomotopyCategory (ComplexShape.up ℤ)).localization
    DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    G.mapDerivedCategory F.mapDerivedCategory⟩

end AlgebraicGeometry
