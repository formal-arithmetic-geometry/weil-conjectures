/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Properness of a coproduct of two schemes

## References

* [Stacks Project, Tag 0CYR](https://stacks.math.columbia.edu/tag/0CYR)
* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/--
For morphisms `p₁ : W₁ ⟶ S` and `p₂ : W₂ ⟶ S`, their coproduct morphism
has the stated open coproduct pieces and is proper when both components are
proper (Stacks, Tags 0CYR and 01JA). -/
theorem proper_coproduct_two
    {S W₁ W₂ : Scheme.{u}} (p₁ : W₁ ⟶ S) (p₂ : W₂ ⟶ S) :
    IsOpenImmersion (coprod.inl : W₁ ⟶ W₁ ⨿ W₂) ∧
      IsOpenImmersion (coprod.inr : W₂ ⟶ W₁ ⨿ W₂) ∧
      IsCompl (Set.range (coprod.inl : W₁ ⟶ W₁ ⨿ W₂))
        (Set.range (coprod.inr : W₂ ⟶ W₁ ⨿ W₂)) ∧
      (∀ [IsProper p₁] [IsProper p₂],
        IsProper (coprod.desc p₁ p₂ : W₁ ⨿ W₂ ⟶ S)) := by
  refine ⟨inferInstance, inferInstance, isCompl_range_inl_inr W₁ W₂, ?_⟩
  intro _ _
  have : IsProper (coprod.map p₁ p₂) :=
    IsZariskiLocalAtTarget.coprodMap (P := @IsProper) p₁ p₂ inferInstance inferInstance
  have : IsProper (coprod.desc (𝟙 S) (𝟙 S)) := inferInstance
  have h : coprod.map p₁ p₂ ≫ coprod.desc (𝟙 S) (𝟙 S) = coprod.desc p₁ p₂ := by
    ext <;> simp
  rw [← h]
  infer_instance

end AlgebraicGeometry
