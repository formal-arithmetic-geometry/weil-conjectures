/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.OpenExtensionDerivedAdjunction
import WeilConjectures.AlgebraicGeometry.OpenExtensionProjectionFormulaAux

/-! # Projection formula for open extension by zero

## References

* Stacks Project, Tags 08BS, 01AK and 06YB.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Use the standard localization on the open scheme. (Stacks, Tag 05RU) -/
local instance openExtensionProjectionStandardDerived (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

set_option maxHeartbeats 500000 in
-- The derived-category elaboration needs a larger reduction budget.
set_option linter.style.haveILetI false in
/-- Exact extension by zero satisfies the tensor projection formula for any
strong monoidal structure on the specified derived restriction functor.
(Stacks, Tags 08BS, 01AK, 06YB and 06YH) -/
theorem exists_openExtension_projectionFormula (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
    ∀ m : R.Monoidal,
      letI := m
      ∃ J : schemeDerivedCategory U.toScheme ⥤ schemeDerivedCategory X,
        ∃ adj : J ⊣ R,
          ∀ (A : schemeDerivedCategory U.toScheme) (K : schemeDerivedCategory X),
            IsIso ((adj.homEquiv (A ⊗ R.obj K) (J.obj A ⊗ K)).symm
              ((adj.unit.app A ⊗ₘ 𝟙 (R.obj K)) ≫
                (Functor.Monoidal.μIso R (J.obj A) K).hom)) := by
  dsimp
  intro m
  letI := m
  obtain ⟨J, ⟨adj⟩⟩ := exists_openExtension_derivedAdjunction X U
  refine ⟨J, adj, ?_⟩
  exact openExtension_projection_formula_of_adjunction X U m J adj

end AlgebraicGeometry
