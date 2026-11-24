/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Uniqueness up to homotopy of lifts into an injective complex

## References

* Stacks Project, Derived Categories, Lemma 13.18.7 (Tag 013S)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Maps into a bounded below complex of injectives are homotopic whenever their
composites with a quasi-isomorphism are homotopic. -/
theorem homotopy_of_comp_quasiIso_of_injective
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L I : CochainComplex C ℤ}
    (hI : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (I.X n))
    [∀ n : ℤ, Injective (I.X n)]
    (α : K ⟶ L) [QuasiIso α]
    (β₁ β₂ : L ⟶ I) (h : Nonempty (Homotopy (α ≫ β₁) (α ≫ β₂))) :
    Nonempty (Homotopy β₁ β₂) := by
  let := HasDerivedCategory.standard C
  obtain ⟨a, ha⟩ := hI
  let : I.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff I a).2 ha
  let : I.IsKInjective := CochainComplex.isKInjective_of_injective I a
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  have hq : DerivedCategory.Q.map (α ≫ β₁) =
      DerivedCategory.Q.map (α ≫ β₂) := DerivedCategory.Q_map_eq_of_homotopy (C := C) h.some
  rw [Functor.map_comp, Functor.map_comp] at hq
  have heq : DerivedCategory.Q.map β₁ = DerivedCategory.Q.map β₂ := by
    exact (cancel_epi (DerivedCategory.Q.map α)).1 hq
  have heq' : q.map β₁ = q.map β₂ := by
    apply (CochainComplex.IsKInjective.Qh_map_bijective (q.obj L) I).1
    rw [← cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app I)]
    rw [DerivedCategory.quotientCompQhIso_hom_naturality,
      DerivedCategory.quotientCompQhIso_hom_naturality]
    simp [heq]
  exact ⟨HomotopyCategory.homotopyOfEq β₁ β₂ heq'⟩

end CochainComplex
