/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosureGeneration

/-!
# Compact generators generate as a localizing subcategory

Let `C` be a triangulated category with coproducts indexed by `Type v` (the universe of its
`Hom`-types), and `P` an essentially small property of objects of `C`, stable under shifts, whose
objects are compact in `C` and detect zero objects of `C`. Then every object of `C` lies in the
localizing closure `Loc(P)`
(`CategoryTheory.ObjectProperty.localizingClosure_eq_top_of_isCompactObj`).

## Implementation details

Objects of `P` are compact in `Loc(P)`, whose coproducts are computed in `C`
(`CategoryTheory.ObjectProperty.isCompactObj_localizingClosure_of_isCompactObj`), so `P`
compactly generates `Loc(P)`, and the inclusion `ι : Loc(P) ⥤ C` has a right adjoint `R` by Brown
representability. For `X` in `C`, composition with the counit `ι R X ⟶ X` is bijective on
morphisms out of the objects of `P`, so it is an isomorphism, because the objects of `P` detect
zero objects of `C`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Pretriangulated Category

namespace CategoryTheory.ObjectProperty

open BrownRepresentability

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {P : ObjectProperty C}

/-- An object of `Loc(P)` which is compact in `C` is compact in `Loc(P)`, whose coproducts are
computed in `C`. -/
lemma isCompactObj_localizingClosure_of_isCompactObj [HasCoproducts.{v} C]
    (X : P.localizingClosure.FullSubcategory) (hX : IsCompactObj X.obj) : IsCompactObj X := by
  intro J Y c hc f
  obtain ⟨S, g, hg⟩ := hX _ (isColimitCofanMkObjOfIsColimit P.localizingClosure.ι _ c.inj
    (hc : IsColimit (Cofan.mk c.pt c.inj))) f.hom
  refine ⟨S, fun j ↦ homMk (g j), P.localizingClosure.ι.map_injective ?_⟩
  rw [Functor.map_sum]
  simpa using hg

/-- **Compact generators generate.** If `C` is triangulated with coproducts indexed by `Type v`,
and `P` is an essentially small property of objects of `C`, stable under shifts, whose objects
are compact in `C` and detect zero objects of `C`, then every object of `C` lies in the
localizing closure `Loc(P)`. -/
theorem localizingClosure_eq_top_of_isCompactObj [IsTriangulated C] [HasCoproducts.{v} C]
    [P.IsStableUnderShift ℤ]
    (hsmall : ∃ (ι : Type v) (S : ι → C), (∀ i, P (S i)) ∧ ∀ X, P X → ∃ i, Nonempty (S i ≅ X))
    (hcompact : ∀ X, P X → IsCompactObj X)
    (hzero : ∀ Y : C, (∀ X, P X → ∀ f : X ⟶ Y, f = 0) → IsZero Y) :
    P.localizingClosure = ⊤ := by
  have hgen : P.CompactlyGeneratesLocalizingClosure :=
    .of_isStableUnderShift hsmall fun X hX ↦
      isCompactObj_localizingClosure_of_isCompactObj X (hcompact X.obj hX)
  obtain ⟨ι, S, hS, -⟩ := hgen.exists_compactGenerators
  have := Functor.isLeftAdjoint_of_compactGenerators hS P.localizingClosure.ι
  let adj := Adjunction.ofIsLeftAdjoint P.localizingClosure.ι
  refine top_unique fun X _ ↦ ?_
  have hiso : IsIso (adj.counit.app X) := by
    obtain ⟨Z, p, δ, hT⟩ := distinguished_cocone_triangle (adj.counit.app X)
    -- composition with the counit is bijective on morphisms out of objects of `Loc(P)`
    have hbij (A : P.localizingClosure.FullSubcategory) :
        Function.Bijective (fun f : A.obj ⟶ _ ↦ f ≫ adj.counit.app X) := by
      have : (fun f : A.obj ⟶ _ ↦ f ≫ adj.counit.app X) =
          (adj.homEquiv A X).symm ∘ fun f ↦ P.localizingClosure.fullyFaithfulι.preimage f := by
        ext f
        rw [Function.comp_apply, Adjunction.homEquiv_counit]
        rfl
      rw [this]
      exact (adj.homEquiv A X).symm.bijective.comp
        P.localizingClosure.fullyFaithfulι.homEquiv.symm.bijective
    refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 (hzero Z fun A hA f ↦ ?_)
    let A' : P.localizingClosure.FullSubcategory :=
      ⟨A⟦(-1 : ℤ)⟧, P.le_localizingClosure _ (P.le_shift (-1) A hA)⟩
    have h₁ : f ≫ δ = 0 := by
      refine eq_zero_of_comp_shift_eq_zero (s' := A'.obj) (Iso.refl _) (adj.counit.app X)
        (fun f' hf' ↦ (hbij A').1 ?_) _ ?_
      · simpa using hf'
      · have : δ ≫ (adj.counit.app X)⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
        rw [assoc, this, comp_zero]
    obtain ⟨f', rfl⟩ := Triangle.coyoneda_exact₃ _ hT f h₁
    obtain ⟨f'', rfl⟩ := (hbij ⟨A, P.le_localizingClosure _ hA⟩).2 f'
    have : adj.counit.app X ≫ p = 0 := comp_distTriang_mor_zero₁₂ _ hT
    simp [this]
  exact P.localizingClosure.prop_of_iso (asIso (adj.counit.app X))
    (P.localizingClosure.ι.rightAdjoint.obj X).property

end CategoryTheory.ObjectProperty
