/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Recognising the counit of a coreflection through a distinguished triangle

Let `F ⊣ G` with `F : D ⥤ C` fully faithful, `C` pretriangulated, and let
`K ⟶ L ⟶ R ⟶ K⟦1⟧` be a distinguished triangle whose first vertex lies in the essential image
of `F` and whose third vertex receives no maps from the shifts of objects of that essential
image. Then `K ⟶ L` *is* the counit `F G L ⟶ L`, up to a unique isomorphism
(`CategoryTheory.Pretriangulated.exists_iso_counit_of_subsingleton`). Consequently a morphism
`ψ : A ⟶ G L` whose transpose `F A ⟶ L` is the first map of such a triangle is an isomorphism
(`CategoryTheory.Pretriangulated.isIso_of_comp_counit_eq_of_subsingleton`).

This is the form in which the supported localization triangle of a closed immersion is used to
recognise the exceptional inverse image `Ri^!`: the second statement shows that a canonical map
into `Ri^! L` is invertible once its transpose is the first map of a distinguished triangle
`Ri_* A ⟶ L ⟶ Rj_* B ⟶`.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type*} [Category* D]

namespace Pretriangulated

/-- **The first map of a triangle is the counit.** Let `F ⊣ G` with `F` fully faithful, and let
`T = (K ⟶ L ⟶ R ⟶ K⟦1⟧)` be distinguished, with `K` in the essential image of `F` and
`Hom((F M)⟦n⟧, R) = 0` for all `M` and `n`. Then there is an isomorphism `e : F G L ≅ K` with
`e.hom ≫ (K ⟶ L)` the counit. -/
theorem exists_iso_counit_of_subsingleton {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
    (hF : F.FullyFaithful) {T : Triangle C} (hT : T ∈ distTriang C)
    (h₃ : ∀ (M : D) (n : ℤ), Subsingleton ((F.obj M)⟦n⟧ ⟶ T.obj₃))
    (h₁ : F.essImage T.obj₁) :
    ∃ e : F.obj (G.obj T.obj₂) ≅ T.obj₁, e.hom ≫ T.mor₁ = adj.counit.app T.obj₂ := by
  have h₀ (M : D) : Subsingleton (F.obj M ⟶ T.obj₃) :=
    have := h₃ M 0
    ((shiftFunctorZero C ℤ).app (F.obj M)).homFromEquiv.symm.subsingleton
  obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ T hT (adj.counit.app T.obj₂)
    ((h₀ (G.obj T.obj₂)).elim _ _)
  -- composing with `T.mor₁` is bijective on maps out of the essential image
  have ha (M : D) : Function.Bijective (fun x : F.obj M ⟶ T.obj₁ ↦ x ≫ T.mor₁) := by
    refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
    · have := h₃ M 1
      exact Triangle.cancel_mor₁_of_subsingleton hT hxy
    · exact (Triangle.coyoneda_exact₂ T hT y ((h₀ M).elim _ _)).imp fun x hx ↦ hx.symm
  have hε (M : D) : Function.Bijective
      (fun x : F.obj M ⟶ F.obj (G.obj T.obj₂) ↦ x ≫ adj.counit.app T.obj₂) := by
    have : (fun x : F.obj M ⟶ F.obj (G.obj T.obj₂) ↦ x ≫ adj.counit.app T.obj₂) =
        (adj.homEquiv _ _).symm ∘ hF.preimage := by
      ext x
      simp [Adjunction.homEquiv_counit]
    rw [this]
    exact (adj.homEquiv _ _).symm.bijective.comp hF.homEquiv.symm.bijective
  have hb' (M : D) : Function.Bijective
      (fun x : F.obj M ⟶ F.obj (G.obj T.obj₂) ↦ x ≫ b) := by
    refine (Function.Bijective.of_comp_iff' (ha M) _).1 ?_
    have : ((fun x : F.obj M ⟶ T.obj₁ ↦ x ≫ T.mor₁) ∘
        fun x : F.obj M ⟶ F.obj (G.obj T.obj₂) ↦ x ≫ b) =
        fun x ↦ x ≫ adj.counit.app T.obj₂ := by
      funext x
      simp [hb]
    rw [this]
    exact hε M
  obtain ⟨N, ⟨e⟩⟩ := h₁
  obtain ⟨s, hs⟩ := (hb' N).2 e.hom
  have hsb : e.inv ≫ s ≫ b = 𝟙 _ := by simp [hs]
  have hbs : b ≫ e.inv ≫ s = 𝟙 _ :=
    (hb' (G.obj T.obj₂)).1 (by dsimp; rw [Category.assoc, Category.assoc, hsb]; simp)
  exact ⟨⟨b, e.inv ≫ s, hbs, by rw [Category.assoc, hsb]⟩, hb.symm⟩

/-- **Recognising an isomorphism onto `G L`.** Let `F ⊣ G` with `F` fully faithful and let
`T = (K ⟶ L ⟶ R ⟶ K⟦1⟧)` be distinguished with `Hom((F M)⟦n⟧, R) = 0` for all `M` and `n`.
If `e : F A ≅ K` and `ψ : A ⟶ G L` are such that `F ψ` followed by the counit is
`e.hom ≫ (K ⟶ L)`, then `ψ` is an isomorphism. -/
theorem isIso_of_comp_counit_eq_of_subsingleton {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
    (hF : F.FullyFaithful) {T : Triangle C} (hT : T ∈ distTriang C)
    (h₃ : ∀ (M : D) (n : ℤ), Subsingleton ((F.obj M)⟦n⟧ ⟶ T.obj₃)) {A : D}
    (e : F.obj A ≅ T.obj₁) (ψ : A ⟶ G.obj T.obj₂)
    (hψ : F.map ψ ≫ adj.counit.app T.obj₂ = e.hom ≫ T.mor₁) : IsIso ψ := by
  obtain ⟨e', he'⟩ := exists_iso_counit_of_subsingleton adj hF hT h₃ ⟨A, ⟨e⟩⟩
  have := h₃ A 1
  have h : F.map ψ ≫ e'.hom = e.hom := Triangle.cancel_mor₁_of_subsingleton hT
    (by rw [Category.assoc, he', hψ])
  have : IsIso (F.map ψ) := by
    rw [show F.map ψ = e.hom ≫ e'.inv by rw [← h]; simp]
    infer_instance
  exact hF.isIso_of_isIso_map ψ

end Pretriangulated

end CategoryTheory
