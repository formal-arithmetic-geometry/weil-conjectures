/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

import WeilConjectures.CategoryTheory.CartanEilenbergConeGradedNormalizedDifferential

/-! # Short-complex comparison for the Cartan--Eilenberg cone filtration

## References

* Stacks Project, Homology, Tag 0133 (canonical augmentation) and Tag 012X
  (column filtration of a total complex).
-/

@[expose] public section

universe uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

private theorem normalized_iso_all_degrees
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (b : ℤ)
    (hIbelow : ∀ s : ℤ, s < b → IsZero (I.X s))
    (hKbelow : ∀ s : ℤ, s < b → IsZero (K.X s))
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (F : DecreasingFiltration (CochainComplex.mappingCone aug))
    (hF : ∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl aug).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Icc (max b p) n).sup (fun s ↦ imageSubobject
          ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
            (ComplexShape.up ℤ) (n - s) s n ≫
              (CochainComplex.mappingCone.inr aug).f n)))
    (p m : ℤ) :
    ∃ e : (F.gradedPiece p).X m ≅ (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).X (m - p),
      CartanEilenbergConeGradedNormalized K I a aug F p m e := by
  by_cases hm : p - 1 ≤ m
  · exact cartanEilenberg_cone_graded_normalized_iso
      K I a b hIbelow hKbelow aug F hF p m hm
  · have hstep : F.complexStep p m = ⊥ := by
      rw [hF]
      have hpm : ¬ p ≤ m + 1 := by omega
      have hIcc : Finset.Icc (max b p) m = ∅ := by
        apply Finset.Icc_eq_empty
        omega
      simp only [ite_eq_right hpm, hIcc, Finset.sup_empty, bot_sup_eq]
    have hzstep : IsZero ((F.step p : CochainComplex A ℤ).X m) := by
      apply IsZero.of_mono_eq_zero ((F.step p).arrow.f m)
      rw [← imageSubobject_arrow_comp ((F.step p).arrow.f m)]
      change factorThruImageSubobject ((F.step p).arrow.f m) ≫
        (F.complexStep p m).arrow = 0
      have harrow : (F.complexStep p m).arrow = 0 := by
        rw [hstep]
        exact Subobject.bot_arrow
      rw [harrow, comp_zero]
    have : Epi (F.complexQuotientπ p (p + 1) (by omega)) := by
      unfold DecreasingFiltration.complexQuotientπ
      infer_instance
    have hzgraded : IsZero ((F.gradedPiece p).X m) :=
      IsZero.of_epi ((F.complexQuotientπ p (p + 1) (by omega)).f m) hzstep
    have hzcolumn : IsZero ((CochainComplex.mappingCone
        (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).X (m - p)) := by
      rw [CochainComplex.mappingCone.isZero_X_iff]
      constructor
      · apply HomologicalComplex.isZero_extend_X
        intro r
        change (r : ℤ) ≠ m - p + 1
        omega
      · apply HomologicalComplex.isZero_extend_X
        intro r
        change (r : ℤ) ≠ m - p
        omega
    refine ⟨hzgraded.iso hzcolumn, ?_⟩
    constructor
    · intro r hr
      omega
    · intro h
      omega

/-- The three terms and two differentials of a graded cone are those of its column cone.
Source: Stacks Project, Homology, Tags 0133 and 012X. -/
theorem cartanEilenberg_cone_graded_shortComplex_iso
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (b : ℤ)
    (hIbelow : ∀ s : ℤ, s < b → IsZero (I.X s))
    (hKbelow : ∀ s : ℤ, s < b → IsZero (K.X s))
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (haug : ∀ n : ℤ, aug.f n = (a.f n).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
        (ComplexShape.up ℤ) 0 n n (zero_add n))
    (F : DecreasingFiltration (CochainComplex.mappingCone aug))
    (hF : ∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl aug).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Icc (max b p) n).sup (fun s ↦ imageSubobject
          ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
            (ComplexShape.up ℤ) (n - s) s n ≫
              (CochainComplex.mappingCone.inr aug).f n)))
    (p n : ℤ) :
    Nonempty ((F.gradedPiece p).sc n ≅
      (CochainComplex.mappingCone
        (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).sc (n - p)) := by
  let D := CochainComplex.mappingCone
    (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)
  let G := F.gradedPiece p
  obtain ⟨e₁, he₁⟩ := normalized_iso_all_degrees
    K I a b hIbelow hKbelow aug F hF p (n - 1)
  obtain ⟨e₂, he₂⟩ := normalized_iso_all_degrees
    K I a b hIbelow hKbelow aug F hF p n
  obtain ⟨e₃, he₃⟩ := normalized_iso_all_degrees
    K I a b hIbelow hKbelow aug F hF p (n + 1)
  have h₁₂ : e₁.inv ≫ G.d (n - 1) n = D.d (n - 1 - p) (n - p) ≫ e₂.inv :=
    cartanEilenberg_cone_graded_normalized_differential
      K I a b hIbelow hKbelow aug haug F hF p (n - 1) n (by omega) e₁ e₂ he₁ he₂
  have h₂₃ : e₂.inv ≫ G.d n (n + 1) = D.d (n - p) (n + 1 - p) ≫ e₃.inv :=
    cartanEilenberg_cone_graded_normalized_differential
      K I a b hIbelow hKbelow aug haug F hF p n (n + 1) rfl e₂ e₃ he₂ he₃
  let E : D.sc' (n - 1 - p) (n - p) (n + 1 - p) ≅ G.sc' (n - 1) n (n + 1) :=
    ShortComplex.isoMk e₁.symm e₂.symm e₃.symm h₁₂ h₂₃
  have hprev : (ComplexShape.up ℤ).prev n = n - 1 := by
    apply ComplexShape.prev_eq'
    change n - 1 + 1 = n
    omega
  have hnext : (ComplexShape.up ℤ).next n = n + 1 := by
    apply ComplexShape.next_eq'
    rfl
  have hprev' : (ComplexShape.up ℤ).prev (n - p) = n - 1 - p := by
    apply ComplexShape.prev_eq'
    change n - 1 - p + 1 = n - p
    omega
  have hnext' : (ComplexShape.up ℤ).next (n - p) = n + 1 - p := by
    apply ComplexShape.next_eq'
    change n - p + 1 = n + 1 - p
    omega
  exact ⟨(G.isoSc' (n - 1) n (n + 1) hprev hnext).trans
    (E.symm.trans (D.isoSc' (n - 1 - p) (n - p) (n + 1 - p) hprev' hnext').symm)⟩

end CategoryTheory.Functor
