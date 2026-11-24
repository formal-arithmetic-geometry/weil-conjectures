/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSplitting
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSplitReindexing

/-!
# Compatibility of sums on explicitly split objects

## References

* Stacks Project, Tag 03SH
* SGA 4, Exposé IX, 5.1
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Sums from two explicit splittings agree after restriction along a commuting square.
No finiteness assumption on `f` is needed: the two finite splittings are supplied.
(Stacks, Section 03SH, after Definition 03SE; SGA 4, Exposé IX, 5.1.) -/
theorem finiteEtaleTrace_split_sum_compatibility {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : Etale f) :
    let B := MorphismProperty.Over.pullback @Etale ⊤ f ⋙ MorphismProperty.Over.map ⊤ hf
    ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (W T₁ T₂ Z : X.Etale) (h₁ : T₁ ⟶ W) (h₂ : T₂ ⟶ W)
      (g₁ : Z ⟶ T₁) (g₂ : Z ⟶ T₂), g₁ ≫ h₁ = g₂ ≫ h₂ →
      ∀ (D₁ : FiniteEtaleTraceSplitting f T₁) (D₂ : FiniteEtaleTraceSplitting f T₂)
        (s : F.obj.obj (op (B.obj W))),
        F.obj.map g₁.op (D₁.sum hf F (F.obj.map (B.map h₁).op s)) =
          F.obj.map g₂.op (D₂.sum hf F (F.obj.map (B.map h₂).op s))  := by
  dsimp only
  intro F W T₁ T₂ Z h₁ h₂ g₁ g₂ he D₁ D₂ s
  obtain ⟨R, hR, hloc⟩ :=
    finiteEtaleTrace_split_reindexing f hf W T₁ T₂ Z h₁ h₂ g₁ g₂ he D₁ D₂
  let P := F.obj ⋙ forget AddCommGrpCat.{u + 1}
  have hP : Presieve.IsSheaf X.smallEtaleTopology P :=
    (isSheaf_iff_isSheaf_of_type X.smallEtaleTopology P).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget X.smallEtaleTopology F.obj
        (forget AddCommGrpCat.{u + 1})).mp F.property)
  apply (hP.isSheafFor R hR).isSeparatedFor.ext
  intro Q k hk
  obtain ⟨e, he⟩ := hloc Q k hk
  let := D₁.finiteIndex
  let := D₂.finiteIndex
  change F.obj.map k.op (F.obj.map g₁.op _) = F.obj.map k.op (F.obj.map g₂.op _)
  simp only [FiniteEtaleTraceSplitting.sum, map_sum]
  apply Fintype.sum_equiv e
  intro j
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rw [he j]

end AlgebraicGeometry.Etale
