/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomRightAdjoint
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # Canonical projection against the restricted scalar unit -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace CategoryTheory.Adjunction
variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
  {F : C ⥤ D} {U : D ⥤ C}

/-- The projection to restricted scalar extension, defined by its adjunction transpose.
Source: the scalar projection formula, Stacks 07A4.
(blueprint: def-per-scalar-closed-projection-data). -/
def scalarUnitProjection [F.OplaxMonoidal] (adj : F ⊣ U) (K : C) :
    K ⊗ U.obj (𝟙_ D) ⟶ U.obj (F.obj K) :=
  adj.homEquiv _ _ (Functor.OplaxMonoidal.δ F K (U.obj (𝟙_ D)) ≫
    F.obj K ◁ adj.counit.app (𝟙_ D) ≫ (ρ_ (F.obj K)).hom)

/-- Restriction identifies the scalar closed Hom with Hom into the restriction.
Source: Stacks 07A6; uniqueness of the composite closed/scalar right adjoints.
(blueprint: def-per-scalar-closed-projection-data). -/
def scalarHomRestrictionIso [F.Monoidal] (adj : F ⊣ U) (K : C) (N : D) :
    U.obj ((ihom (F.obj K)).obj N) ≅ (ihom K).obj (U.obj N) :=
  ((adj.ihomCompIso K).app N).symm

end CategoryTheory.Adjunction
