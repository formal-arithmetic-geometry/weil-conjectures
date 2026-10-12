/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Maps into bounded below complexes of injectives

If `α : K ⟶ L` is a quasi-isomorphism and `I` is a bounded below complex of injective objects,
then two morphisms `L ⟶ I` whose composites with `α` are homotopic are themselves homotopic.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Let `α : K ⟶ L` be a quasi-isomorphism of cochain complexes and `I` a bounded below complex
(`I.IsStrictlyGE d`) of injective objects. If `β₁ β₂ : L ⟶ I` are such that `α ≫ β₁` and
`α ≫ β₂` are homotopic, then `β₁` and `β₂` are homotopic.
(blueprint: `lem-weil-pbc-lift-to-injective-unique-up-to-homotopy`) -/
theorem homotopy_of_comp_quasiIso_of_injective {K L I : CochainComplex C ℤ} (d : ℤ)
    [I.IsStrictlyGE d] [∀ n, Injective (I.X n)] (α : K ⟶ L) [QuasiIso α] (β₁ β₂ : L ⟶ I)
    (h : Homotopy (α ≫ β₁) (α ≫ β₂)) : Nonempty (Homotopy β₁ β₂) := by
  let := HasDerivedCategory.standard C
  have := isKInjective_of_injective I d
  have e : ∀ β : L ⟶ I, DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map β) =
      (DerivedCategory.quotientCompQhIso C).hom.app L ≫ DerivedCategory.Q.map β ≫
        (DerivedCategory.quotientCompQhIso C).inv.app I := by
    intro β
    rw [← DerivedCategory.quotientCompQhIso_hom_naturality_assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have hQ : DerivedCategory.Q.map β₁ = DerivedCategory.Q.map β₂ := by
    rw [← cancel_epi (DerivedCategory.Q.map α), ← Functor.map_comp, ← Functor.map_comp]
    exact DerivedCategory.Q_map_eq_of_homotopy (C := C) h
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
  apply (IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient _ _).obj L) I).1
  rw [e, e, hQ]

end CochainComplex
