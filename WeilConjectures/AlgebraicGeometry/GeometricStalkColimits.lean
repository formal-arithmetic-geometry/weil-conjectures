/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Colimits and geometric stalks

Reference: Stacks Project, Tags 03PN and 04K1.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The geometric stalk of sheaves of abelian groups on the small etale site of a scheme `T` at a
geometric point `s` commutes with arbitrary colimits, also for complexes of abelian sheaves
degreewise (Stacks, Tags 03PN and 04K1). -/
theorem geometricStalk_preservesColimits
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ T) :
    PreservesColimits
      ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u} ℤ)) ∧
    PreservesColimits
      (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u} ℤ)).mapHomologicalComplex
        (ComplexShape.up ℤ)) := by
  refine ⟨inferInstance, ⟨?_⟩⟩
  intro J _
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u} ℤ)) :=
    Limits.comp_preservesFilteredColimits
      (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u})
      (CategoryTheory.forget AddCommGrpCat.{u})
  infer_instance

end AlgebraicGeometry.Scheme
