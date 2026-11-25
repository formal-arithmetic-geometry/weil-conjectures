/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosureGeneration

/-! # Shifted generators detect isomorphisms on their localizing closure

A morphism between objects of the localizing closure of a class `S` of objects of a
triangulated category is an isomorphism as soon as postcomposition with it is bijective on Hom
from every integer shift of every object of `S`.

## Implementation details

The class of generators is an arbitrary object property. The localizing closure is the existing
intersection of replete triangulated subcategories closed under coproducts indexed in the Hom
universe; neither smallness nor compactness of the generator class is required.

The proof completes `α : B ⟶ G` to a distinguished triangle `B ⟶ G ⟶ K ⟶ B[1]`, so that `K`
lies in the localizing closure, and shows that every shifted generator has only zero maps to
`K`. The left orthogonal of the shifts of `K` is then a replete triangulated subcategory closed
under coproducts containing the generators, hence contains `K`, so `K` is zero and `α` is an
isomorphism. No coproduct indexed by the generator class is used.

## References

* [Stacks, Tags 0145, 0146, 0149, 0FXC and 05QR]
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

/-- A morphism between objects of the localizing closure of an arbitrary class is invertible
if postcomposition induces bijections on Hom from every integer shift of every generator. -/
theorem isIso_of_bijective_postcomp_shift_generators
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [HasCoproducts.{v} C] (S : ObjectProperty C) {B G : C} (α : B ⟶ G)
    (hB : S.localizingClosure B) (hG : S.localizingClosure G)
    (hα : ∀ (X : C), S X → ∀ (n : ℤ),
      Function.Bijective (fun (f : X⟦n⟧ ⟶ B) ↦ f ≫ α)) : IsIso α := by
  let P := S.shiftClosure ℤ
  have hpost : ∀ (X : C), P X →
      Function.Bijective (fun (f : X ⟶ B) ↦ f ≫ α) := by
    rintro X ⟨Y, n, e, hY⟩
    constructor
    · intro f g h
      apply (cancel_epi e.inv).mp
      apply (hα Y hY n).injective
      simpa only [Category.assoc] using congrArg (fun k ↦ e.inv ≫ k) h
    · intro g
      obtain ⟨f, hf⟩ := (hα Y hY n).surjective (e.inv ≫ g)
      refine ⟨e.hom ≫ f, ?_⟩
      dsimp only at hf ⊢
      rw [Category.assoc, hf, e.hom_inv_id_assoc]
  obtain ⟨K, p, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle α
  let T := Pretriangulated.Triangle.mk α p δ
  have hK : S.localizingClosure K :=
    S.localizingClosure.ext_of_isTriangulatedClosed₃ T hT hB hG
  have hvan : ∀ (X : C), P X → ∀ (f : X ⟶ K), f = 0 := by
    intro X hX f
    have hδ : f ≫ δ = 0 := by
      let adj := (shiftEquiv' C (-1 : ℤ) 1 (by simp)).toAdjunction
      let g := (adj.homEquiv X B).symm (f ≫ δ)
      have hg : g ≫ α = 0 := by
        apply (adj.homEquiv X G).injective
        rw [adj.homEquiv_naturality_right]
        simp only [g, Equiv.apply_symm_apply, Adjunction.homEquiv_unit,
          Functor.map_zero, comp_zero]
        change (f ≫ δ) ≫ α⟦(1 : ℤ)⟧' = 0
        have hcomp : δ ≫ α⟦(1 : ℤ)⟧' = 0 :=
          Pretriangulated.comp_distTriang_mor_zero₃₁ T hT
        rw [Category.assoc, hcomp, comp_zero]
      have hg₀ : g = 0 :=
        (hpost _ (P.le_shift (-1 : ℤ) X hX)).injective (by simpa using hg)
      rw [← (adj.homEquiv X B).apply_symm_apply (f ≫ δ)]
      change (adj.homEquiv X B) g = 0
      simp [hg₀, Adjunction.homEquiv_unit]
    obtain ⟨g, hg⟩ := T.coyoneda_exact₃ hT f hδ
    obtain ⟨h, rfl⟩ := (hpost X hX).surjective g
    rw [hg]
    change (h ≫ α) ≫ p = 0
    have hcomp : α ≫ p = 0 := Pretriangulated.comp_distTriang_mor_zero₁₂ T hT
    rw [Category.assoc, hcomp, comp_zero]
  have hS : S ≤ (shiftsOf K).leftOrthogonal := by
    rintro X hX W f ⟨n, ⟨e⟩⟩
    let adj := (shiftEquiv' C (-n) n (by simp)).toAdjunction
    have h₀ := hvan (X⟦-n⟧) ⟨X, -n, Iso.refl _, hX⟩
      ((adj.homEquiv X K).symm (f ≫ e.hom))
    rw [← cancel_mono e.hom, zero_comp,
      ← (adj.homEquiv X K).apply_symm_apply (f ≫ e.hom), h₀]
    simp [Adjunction.homEquiv_unit]
  have hzero : IsZero K := by
    rw [IsZero.iff_id_eq_zero]
    exact S.localizingClosure_le hS K hK (𝟙 K)
      ⟨0, ⟨(shiftFunctorZero C ℤ).symm.app K⟩⟩
  exact (T.isZero₃_iff_isIso₁ hT).mp hzero

end CategoryTheory.ObjectProperty
