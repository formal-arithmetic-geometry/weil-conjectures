/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.Filtration

/-!
# Induction over finite filtrations

A filtered morphism inducing isomorphisms on all graded pieces of finite filtrations is an
isomorphism, as are the induced maps on filtration steps.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace WeilFilteredObject

/-- The restriction of a filtered morphism to the `p`-th filtration steps. -/
noncomputable def restriction {A B : WeilFilteredObject C} (f : Hom A B) (p : ℤ) :
    (A.filtration.F p : C) ⟶ (B.filtration.F p : C) :=
  Classical.choose (f.preserves p)

/-- A filtered morphism induces a map on the `p`-th graded pieces compatible with the
restriction to the `p`-th steps. -/
theorem exists_gradedMap (A B : WeilFilteredObject C) (f : Hom A B) (p : ℤ) :
    ∃ g : A.filtration.gr p ⟶ B.filtration.gr p,
      cokernel.π (Subobject.ofLE (A.filtration.F (p + 1))
        (A.filtration.F p) (A.filtration.antitone (by omega))) ≫ g =
        restriction f p ≫ cokernel.π (Subobject.ofLE (B.filtration.F (p + 1))
          (B.filtration.F p) (B.filtration.antitone (by omega))) := by
  sorry

/-- The map on the `p`-th graded pieces induced by a filtered morphism. -/
noncomputable def gradedMap {A B : WeilFilteredObject C} (f : Hom A B) (p : ℤ) :
    A.filtration.gr p ⟶ B.filtration.gr p :=
by
  have restriction_arrow {A B : WeilFilteredObject C} (f : Hom A B) (p : ℤ) :
      restriction f p ≫ (B.filtration.F p).arrow =
        (A.filtration.F p).arrow ≫ f.hom :=
    Classical.choose_spec (f.preserves p)
  have restriction_naturality {A B : WeilFilteredObject C} (f : Hom A B) (p : ℤ) :
      Subobject.ofLE (A.filtration.F (p + 1)) (A.filtration.F p)
          (A.filtration.antitone (by omega)) ≫ restriction f p =
        restriction f (p + 1) ≫ Subobject.ofLE (B.filtration.F (p + 1))
          (B.filtration.F p) (B.filtration.antitone (by omega)) := by
    rw [← cancel_mono (B.filtration.F p).arrow]
    simp only [Category.assoc, restriction_arrow, Subobject.ofLE_arrow]
    rw [← Category.assoc, Subobject.ofLE_arrow]
  have exists_gradedMap (A B : WeilFilteredObject C) (f : Hom A B) (p : ℤ) :
      ∃ g : A.filtration.gr p ⟶ B.filtration.gr p,
        cokernel.π (Subobject.ofLE (A.filtration.F (p + 1))
          (A.filtration.F p) (A.filtration.antitone (by omega))) ≫ g =
          restriction f p ≫ cokernel.π (Subobject.ofLE (B.filtration.F (p + 1))
            (B.filtration.F p) (B.filtration.antitone (by omega))) := by
    let iA := Subobject.ofLE (A.filtration.F (p + 1)) (A.filtration.F p)
      (A.filtration.antitone (by omega))
    let iB := Subobject.ofLE (B.filtration.F (p + 1)) (B.filtration.F p)
      (B.filtration.antitone (by omega))
    have hw : iA ≫ (restriction f p ≫ cokernel.π iB) = 0 := by
      rw [← Category.assoc, restriction_naturality, Category.assoc, cokernel.condition,
        comp_zero]
    exact ⟨cokernel.desc iA (restriction f p ≫ cokernel.π iB) hw,
      cokernel.π_desc _ _ _⟩
  exact Classical.choose (exists_gradedMap A B f p)

/-- A filtered morphism between objects with finite filtrations that induces isomorphisms on
all graded pieces is an isomorphism, and restricts to isomorphisms on all filtration steps. -/
theorem finite_filtration_induction (A B : WeilFilteredObject C) (f : Hom A B)
    (hA : A.filtration.IsFinite) (hB : B.filtration.IsFinite)
    (hgraded : ∀ p : ℤ, IsIso (gradedMap f p)) :
    IsIso f.hom ∧ ∀ p : ℤ, IsIso (restriction f p) := by
  sorry

end WeilFilteredObject

end CategoryTheory
