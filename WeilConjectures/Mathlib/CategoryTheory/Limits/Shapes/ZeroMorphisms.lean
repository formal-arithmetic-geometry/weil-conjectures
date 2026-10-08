/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Copowers along an injection of index types

In a category with zero morphisms, an injection `f : ι → ι'` induces a split monomorphism
between the copowers `∐ (fun (_ : ι) ↦ X) ⟶ ∐ (fun (_ : ι') ↦ X)` of an object `X`: the
retraction sends the summand indexed by `s : ι'` to the summand indexed by the (unique)
antecedent of `s`, if there is one, and to zero otherwise.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The morphism between copowers of `X : C` induced by an injection `f : ι → ι'` of index
types is a split monomorphism. -/
lemma isSplitMono_sigmaDesc_of_injective (X : C) {ι ι' : Type*} (f : ι → ι')
    (hf : Function.Injective f) [HasCoproduct (fun (_ : ι) ↦ X)]
    [HasCoproduct (fun (_ : ι') ↦ X)] :
    IsSplitMono (Sigma.desc (fun (i : ι) ↦ Sigma.ι (fun (_ : ι') ↦ X) (f i))) := by
  classical
  refine ⟨⟨Sigma.desc
    (fun s ↦ if h : ∃ i, f i = s then Sigma.ι (fun (_ : ι) ↦ X) h.choose else 0), ?_⟩⟩
  ext i
  have h : ∃ j, f j = f i := ⟨i, rfl⟩
  rw [← Category.assoc, Sigma.ι_desc, Sigma.ι_desc, dif_pos h, hf h.choose_spec,
    Category.comp_id]

/-- If `f : ι → ι'` is injective, then the copower `∐ (fun (_ : ι') ↦ X)` admits an
epimorphism onto the copower `∐ (fun (_ : ι) ↦ X)`. -/
lemma exists_epi_copower_of_injective (X : C) {ι ι' : Type*} (f : ι → ι')
    (hf : Function.Injective f) [HasCoproduct (fun (_ : ι) ↦ X)]
    [HasCoproduct (fun (_ : ι') ↦ X)] :
    ∃ (r : (∐ fun (_ : ι') ↦ X) ⟶ (∐ fun (_ : ι) ↦ X)), Epi r := by
  have := isSplitMono_sigmaDesc_of_injective X f hf
  refine ⟨retraction (Sigma.desc (fun (i : ι) ↦ Sigma.ι (fun (_ : ι') ↦ X) (f i))), ?_⟩
  have : IsSplitEpi (retraction (Sigma.desc
    (fun (i : ι) ↦ Sigma.ι (fun (_ : ι') ↦ X) (f i)))) := ⟨⟨_, IsSplitMono.id _⟩⟩
  infer_instance

end CategoryTheory.Limits
