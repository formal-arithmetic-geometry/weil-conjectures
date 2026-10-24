/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveDevissage

/-!
# Full faithfulness on shifted sums

Let `F : D(C) ⥤ D(D)` be an additive functor commuting with the shifts. The property that `F` is
bijective on the morphisms `M ⟶ N` (`CategoryTheory.Functor.HomBijective`) is stable under
isomorphisms, binary biproducts and shifts in both variables, and holds when `M` or `N` is zero.
Hence, if `F` is bijective on the morphisms `X[0] ⟶ Y[0]⟦b⟧` for all objects `X`, `Y` satisfying a
property `R`, it is bijective on the morphisms between shifted sums of objects satisfying `R`
(`DerivedCategory.homBijective_of_isShiftSum`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

/-- The functor `F` is bijective on the morphisms `M ⟶ N`. -/
def HomBijective (M N : C) : Prop :=
  Function.Bijective (fun φ : M ⟶ N ↦ F.map φ)

variable {F}

lemma HomBijective.of_iso_left {M M' N : C} (h : F.HomBijective M N) (e : M ≅ M') :
    F.HomBijective M' N := by
  refine ⟨fun φ ψ hφψ ↦ ?_, fun χ ↦ ?_⟩
  · refine (cancel_epi e.hom).1 (h.1 ?_)
    simp only [F.map_comp]
    exact congrArg (F.map e.hom ≫ ·) hφψ
  · obtain ⟨ψ, hψ⟩ := h.2 (F.map e.hom ≫ χ)
    refine ⟨e.inv ≫ ψ, ?_⟩
    simp only [F.map_comp] at hψ ⊢
    rw [hψ, ← Category.assoc, ← F.map_comp, e.inv_hom_id, F.map_id, Category.id_comp]

lemma HomBijective.of_iso_right {M N N' : C} (h : F.HomBijective M N) (e : N ≅ N') :
    F.HomBijective M N' := by
  refine ⟨fun φ ψ hφψ ↦ ?_, fun χ ↦ ?_⟩
  · refine (cancel_mono e.inv).1 (h.1 ?_)
    simp only [F.map_comp]
    exact congrArg (· ≫ F.map e.inv) hφψ
  · obtain ⟨ψ, hψ⟩ := h.2 (χ ≫ F.map e.inv)
    refine ⟨ψ ≫ e.hom, ?_⟩
    simp only [F.map_comp] at hψ ⊢
    rw [hψ, Category.assoc, ← F.map_comp, e.inv_hom_id, F.map_id, Category.comp_id]

variable [Preadditive C] [Preadditive D] [F.Additive]

lemma HomBijective.of_isZero_left {M N : C} (hM : IsZero M) : F.HomBijective M N :=
  ⟨fun _ _ _ ↦ hM.eq_of_src _ _, fun _ ↦ ⟨0, ((F.map_isZero hM).eq_of_src _ _)⟩⟩

lemma HomBijective.of_isZero_right {M N : C} (hN : IsZero N) : F.HomBijective M N :=
  ⟨fun _ _ _ ↦ hN.eq_of_tgt _ _, fun _ ↦ ⟨0, ((F.map_isZero hN).eq_of_tgt _ _)⟩⟩

lemma HomBijective.biprod_left [HasBinaryBiproducts C] {M₁ M₂ N : C} (h₁ : F.HomBijective M₁ N)
    (h₂ : F.HomBijective M₂ N) : F.HomBijective (M₁ ⊞ M₂) N := by
  refine ⟨fun φ ψ hφψ ↦ ?_, fun χ ↦ ?_⟩
  · refine biprod.hom_ext' _ _ (h₁.1 ?_) (h₂.1 ?_) <;>
      simp only [F.map_comp] <;> exact congrArg (_ ≫ ·) hφψ
  · obtain ⟨φ₁, hφ₁⟩ := h₁.2 (F.map biprod.inl ≫ χ)
    obtain ⟨φ₂, hφ₂⟩ := h₂.2 (F.map biprod.inr ≫ χ)
    refine ⟨biprod.desc φ₁ φ₂, ?_⟩
    simp only at hφ₁ hφ₂ ⊢
    rw [biprod.desc_eq, F.map_add, F.map_comp, F.map_comp, hφ₁, hφ₂, ← Category.assoc,
      ← Category.assoc, ← F.map_comp, ← F.map_comp, ← Preadditive.add_comp, ← F.map_add,
      biprod.total, F.map_id, Category.id_comp]

lemma HomBijective.biprod_right [HasBinaryBiproducts C] {M N₁ N₂ : C} (h₁ : F.HomBijective M N₁)
    (h₂ : F.HomBijective M N₂) : F.HomBijective M (N₁ ⊞ N₂) := by
  refine ⟨fun φ ψ hφψ ↦ ?_, fun χ ↦ ?_⟩
  · refine biprod.hom_ext _ _ (h₁.1 ?_) (h₂.1 ?_) <;>
      simp only [F.map_comp] <;> exact congrArg (· ≫ _) hφψ
  · obtain ⟨φ₁, hφ₁⟩ := h₁.2 (χ ≫ F.map biprod.fst)
    obtain ⟨φ₂, hφ₂⟩ := h₂.2 (χ ≫ F.map biprod.snd)
    refine ⟨biprod.lift φ₁ φ₂, ?_⟩
    simp only at hφ₁ hφ₂ ⊢
    rw [biprod.lift_eq, F.map_add, F.map_comp, F.map_comp, hφ₁, hφ₂, Category.assoc,
      Category.assoc, ← F.map_comp, ← F.map_comp, ← Preadditive.comp_add, ← F.map_add,
      biprod.total, F.map_id, Category.comp_id]

omit [Preadditive C] [Preadditive D] [F.Additive] in
lemma HomBijective.shift {A : Type*} [AddGroup A] [HasShift C A] [HasShift D A] [F.CommShift A]
    {M N : C} (h : F.HomBijective M N) (a : A) :
    F.HomBijective ((shiftFunctor C a).obj M) ((shiftFunctor C a).obj N) := by
  have hF (φ : M ⟶ N) : F.map ((shiftFunctor C a).map φ) =
      (F.commShiftIso a).hom.app M ≫ (shiftFunctor D a).map (F.map φ) ≫
        (F.commShiftIso a).inv.app N := by
    rw [← Category.assoc, ← F.commShiftIso_hom_naturality, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have hC : Function.Bijective (fun φ : M ⟶ N ↦ (shiftFunctor C a).map φ) :=
    (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor C a)).map_bijective M N
  have hD : Function.Bijective
      (fun φ : F.obj M ⟶ F.obj N ↦ (shiftFunctor D a).map φ) :=
    (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor D a)).map_bijective _ _
  have hconj : Function.Bijective (fun χ : (shiftFunctor D a).obj (F.obj M) ⟶
      (shiftFunctor D a).obj (F.obj N) ↦
        (F.commShiftIso a).hom.app M ≫ χ ≫ (F.commShiftIso a).inv.app N) :=
    ((F.commShiftIso a).app M |>.homCongr ((F.commShiftIso a).app N)).symm.bijective
  have hcomp : (fun φ ↦ F.map φ) ∘ (fun φ : M ⟶ N ↦ (shiftFunctor C a).map φ) =
      (fun χ ↦ (F.commShiftIso a).hom.app M ≫ χ ≫ (F.commShiftIso a).inv.app N) ∘
        (fun φ ↦ (shiftFunctor D a).map φ) ∘ (fun φ ↦ F.map φ) := by
    ext1 φ
    exact hF φ
  exact (Function.Bijective.of_comp_iff _ hC).1 (hcomp ▸ hconj.comp (hD.comp h))

end CategoryTheory.Functor

namespace DerivedCategory

variable {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [Category D] [Abelian D]
  [HasDerivedCategory D] {F : DerivedCategory C ⥤ DerivedCategory D} [F.Additive] [F.CommShift ℤ]
  {R : ObjectProperty C}

/-- If `F` is bijective on the morphisms `X[0] ⟶ Y[0]⟦b⟧` for all objects `X`, `Y` satisfying
`R`, then it is bijective on the morphisms between shifted sums of objects satisfying `R`. -/
theorem homBijective_of_isShiftSum
    (hbase : ∀ X Y, R X → R Y → ∀ b : ℤ,
      F.HomBijective ((singleFunctor C 0).obj X)
        ((shiftFunctor _ b).obj ((singleFunctor C 0).obj Y)))
    {M N : DerivedCategory C} (hM : IsShiftSum R M) (hN : IsShiftSum R N) :
    F.HomBijective M N := by
  let Q₂ : ObjectProperty (DerivedCategory C) := fun N' ↦
    ∀ M', IsShiftSum R M' → F.HomBijective M' N'
  have : Q₂.IsClosedUnderIsomorphisms := ⟨fun e h M' hM' ↦ (h M' hM').of_iso_right e⟩
  refine hN.prop Q₂ (fun N' hN' M' _ ↦ .of_isZero_right hN')
    (fun N₁ N₂ h₁ h₂ M' hM' ↦ (h₁ M' hM').biprod_right (h₂ M' hM')) (fun N' n h M' hM' ↦ ?_)
    (fun Y hY M' hM' ↦ ?_) M hM
  · exact ((h _ (hM'.shift (-n))).shift n).of_iso_left
      ((shiftFunctorCompIsoId _ (-n) n (by lia)).app M')
  · let Q₁ : ObjectProperty (DerivedCategory C) := fun M'' ↦
      ∀ b : ℤ, F.HomBijective M'' ((shiftFunctor _ b).obj ((singleFunctor C 0).obj Y))
    have : Q₁.IsClosedUnderIsomorphisms := ⟨fun e h b ↦ (h b).of_iso_left e⟩
    have h := hM'.prop Q₁ (fun _ hM'' _ ↦ .of_isZero_left hM'')
      (fun _ _ h₁ h₂ b ↦ (h₁ b).biprod_left (h₂ b))
      (fun M'' n h b ↦ ((h (b - n)).shift n).of_iso_right
        ((shiftFunctorAdd' _ (b - n) n b (by lia)).app _).symm)
      (fun X hX b ↦ hbase X Y hX hY b)
    exact (h 0).of_iso_right ((shiftFunctorZero _ ℤ).app _)

end DerivedCategory
