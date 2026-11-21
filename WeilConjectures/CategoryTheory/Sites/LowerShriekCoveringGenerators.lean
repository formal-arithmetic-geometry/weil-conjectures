/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability

/-!
# A left adjoint from corepresentable evaluations on covering generators

Source: Stacks Project, Sites, Tag 09YX.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- A geometric inverse image has a left adjoint if its evaluations on a covering set
of site objects are corepresentable.

Source: Stacks Project, Sites, Tag 09YX. -/
theorem exists_leftAdjoint_of_covering_corepresentable_evaluations
    {C : Type u} [SmallCategory C] {D : Type v} [SmallCategory D]
    (J : Precoverage C) [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (K : Precoverage D) [K.HasIsos] [K.IsStableUnderComposition]
    [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (R : Sheaf J.toGrothendieck (Type (max u v w)) ⥤
      Sheaf K.toGrothendieck (Type (max u v w)))
    (fStar : Sheaf K.toGrothendieck (Type (max u v w)) ⥤
      Sheaf J.toGrothendieck (Type (max u v w)))
    (hadj : R ⊣ fStar) [PreservesFiniteLimits R]
    (E : Set D)
    (hcover : ∀ V : D, ∃ S : Presieve V, S ∈ K V ∧
      ∀ (W : D) (g : W ⟶ V), S g → W ∈ E)
    (hrep : ∀ V ∈ E, ∃ G : Sheaf J.toGrothendieck (Type (max u v w)),
      Nonempty (coyoneda.obj (op G) ≅
        R ⋙ (sheafSections K.toGrothendieck (Type (max u v w))).obj (op V))) :
    ∃ L : Sheaf K.toGrothendieck (Type (max u v w)) ⥤
      Sheaf J.toGrothendieck (Type (max u v w)), Nonempty (L ⊣ R) := by
  have _ := hadj
  have hdefined : ∀ H : Sheaf K.toGrothendieck (Type (max u v w)),
      R.leftAdjointObjIsDefined H :=
    leftAdjointObjIsDefined_of_covering_corepresentable_evaluations
      J K R E hcover hrep
  have htop : R.leftAdjointObjIsDefined = ⊤ := by
    ext H
    simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
    exact hdefined H
  have : R.IsRightAdjoint :=
    Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top htop
  exact ⟨R.leftAdjoint, ⟨Adjunction.ofIsRightAdjoint R⟩⟩

end CategoryTheory
