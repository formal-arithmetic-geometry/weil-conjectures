/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Sheaf.CategoryTheory.SiteCechComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Čech acyclicity of injective sheaves on a site

Source: Stacks Project, Cohomology on Sites, Tags 03AW, 03F6, 03AS, 03AT, 03AU,
03AN (blueprint: lem-weil-pbc-site-injective-cech-acyclic).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- An injective abelian sheaf has vanishing positive Čech cohomology on every covering,
and degree-zero Čech cohomology is its sections on the covered object.
(blueprint: lem-weil-pbc-site-injective-cech-acyclic) -/
theorem site_injective_cech_acyclic
    {C : Type u} [Category.{v} C]
    {J : Precoverage C} [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    {T : Type w} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (hcover : Presieve.ofArrows f hom ∈ J U)
    (S : SiteCechComplex f hom)
    (I : Sheaf J.toGrothendieck AddCommGrpCat.{w}) [Injective I] :
    (∀ p : ℕ, 0 < p → IsZero ((S.cohomologyFunctor p).obj I.obj)) ∧
      Nonempty (((S.cohomologyFunctor 0).obj I.obj) ≅
        I.obj.obj (op U)) := by
  sorry

end CategoryTheory
