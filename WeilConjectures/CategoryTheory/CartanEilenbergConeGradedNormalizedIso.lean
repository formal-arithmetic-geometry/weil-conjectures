/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import WeilConjectures.CategoryTheory.CartanEilenbergConeGradedSplitInjection
import WeilConjectures.CategoryTheory.CartanEilenbergConeGradedHomExt

/-! # Normalized degreewise comparison for the Cartan--Eilenberg cone filtration

## References

* Stacks Project, Homology, Tag 0133 (canonical augmentation) and Tag 012X
  (column filtration of a total complex).
-/

@[expose] public section

universe uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

/-- The inverse comparison is normalized by the actual column inclusions.
The lifts are unique because the filtration inclusion is monic. These equations
fix the comparison on both cone summands, and exclude arbitrary automorphisms.
Source: Stacks, Tags 012X and 0133, retained-column quotient construction. -/
def CartanEilenbergConeGradedNormalized
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (F : DecreasingFiltration (CochainComplex.mappingCone aug)) (p m : ℤ)
    (e : (F.gradedPiece p).X m ≅ (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).X (m - p)) :
    Prop :=
  (∀ (r : ℕ) (h : (r : ℤ) + p = m),
    ∃ l : (I.X p).X r ⟶ (F.step p : CochainComplex A ℤ).X m,
      l ≫ (F.step p).arrow.f m =
        (HomologicalComplex.extendXIso
          (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p))
          ComplexShape.embeddingUpNat (i := r) (i' := m - p)
          (by change (r : ℤ) = m - p; omega)).inv ≫
        (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
          (ComplexShape.up ℤ) (m - p) p m (by change (m - p) + p = m; omega) ≫
        (CochainComplex.mappingCone.inr aug).f m ∧
      l ≫ (F.complexQuotientπ p (p + 1) (by omega)).f m =
        (HomologicalComplex.extendXIso (I.X p) ComplexShape.embeddingUpNat
          (i := r) (i' := m - p)
          (by change (r : ℤ) = m - p; omega)).inv ≫
        (CochainComplex.mappingCone.inr
          (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).f (m - p) ≫
        e.inv) ∧
  (∀ h : m + 1 = p,
    ∃ l : K.X p ⟶ (F.step p : CochainComplex A ℤ).X m,
      l ≫ (F.step p).arrow.f m =
        (K.XIsoOfEq h.symm).hom ≫
        (CochainComplex.mappingCone.inl aug).v (m + 1) m (by omega) ∧
      l ≫ (F.complexQuotientπ p (p + 1) (by omega)).f m =
        (HomologicalComplex.extendXIso ((CochainComplex.single₀ A).obj (K.X p))
          ComplexShape.embeddingUpNat (i := 0) (i' := m - p + 1)
          (by change (0 : ℤ) = m - p + 1; omega)).inv ≫
        (CochainComplex.mappingCone.inl
          (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).v
          (m - p + 1) (m - p) (by omega) ≫ e.inv)

/-- In the possible support range, the column-tail quotient has a normalized isomorphism.
Source: Stacks Project, Tags 012X and 0133. -/
theorem cartanEilenberg_cone_graded_normalized_iso
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
    (p m : ℤ) (hm : p - 1 ≤ m) :
    ∃ e : (F.gradedPiece p).X m ≅ (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).X (m - p),
      CartanEilenbergConeGradedNormalized K I a aug F p m e := by
  obtain ⟨v, ⟨u, hu⟩, hv⟩ := cartanEilenberg_cone_graded_split_injection
    K I a b hIbelow hKbelow aug F hF p m hm
  have : IsSplitMono v := IsSplitMono.mk' ⟨u, hu⟩
  have : Epi v := by
    constructor
    intro T g h w
    apply cartanEilenberg_cone_graded_hom_ext
      K I b aug F hF p m hm T g h
    · intro r hr l hl
      obtain ⟨l', hl', hq⟩ := hv.1 r hr
      have he : l = l' := (cancel_mono ((F.step p).arrow.f m)).1 (hl.trans hl'.symm)
      subst l
      simp only [← Category.assoc]
      simp only [hq, Category.assoc, w]
    · intro hk l hl
      obtain ⟨l', hl', hq⟩ := hv.2 hk
      have he : l = l' := (cancel_mono ((F.step p).arrow.f m)).1 (hl.trans hl'.symm)
      subst l
      simp only [← Category.assoc]
      simp only [hq, Category.assoc, w]
  have : IsIso v := isIso_of_mono_of_epi v
  exact ⟨(asIso v).symm, hv⟩

end CategoryTheory.Functor
