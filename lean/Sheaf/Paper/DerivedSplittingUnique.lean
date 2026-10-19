/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.Algebra.Homology.PreciseVanishing

/-!
# Splitting and uniqueness for a derived triangle with separated degrees

Source: Stacks Project, More on Algebra, Tag 0BCG (blueprint:
lem-pc-derived-splitting-unique).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace CategoryTheory

variable {R : Type u} [Ring R]
variable [HasDerivedCategory.{w} (ModuleCat.{v} R)]

/--
(blueprint: lem-pc-derived-splitting-unique) For a bounded projective complex
concentrated in degrees `[a,b]`, maps to an object with homology vanishing in
degrees at least `a` vanish.  Vanishing in degrees at least `a + 1` splits every
distinguished triangle with this object as its third term, and the splitting is
unique under the stronger vanishing.  This is the statement of Stacks Project,
More on Algebra, Tag 0BCG. Choose a bounded projective representative of `L`.
First, the precise projective-complex vanishing lemma
`lem-pc-ring-precise-vanishing` gives `Hom(L,K) = 0` when the homology of `K`
vanishes in degrees at least `a`. Second, under vanishing from `a + 1`, the
homology of `K[1]` vanishes from `a`, so the same lemma makes the triangle's
connecting map `L ⟶ K[1]` zero. Third, the zero-third-map biproduct criterion
`lem-pc-derived-zero-third-split` gives the compatible isomorphism. Finally,
under vanishing from `a`, the first step gives `Hom(L,K) = 0`; the difference
between two compatible splittings has only an `L ⟶ K` off-diagonal entry,
which is zero, so the splittings agree.
-/
theorem derivedSplittingUnique
    (a b : ℤ) (K L : DerivedCategory (ModuleCat.{v} R))
    (hL : ∃ P : CochainComplex (ModuleCat.{v} R) ℤ,
      (∀ i : ℤ, Projective (P.X i)) ∧
        (∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i)) ∧
        Nonempty (L ≅ DerivedCategory.Q.obj P)) :
    ((∀ i : ℤ, a ≤ i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) →
      ∀ f : L ⟶ K, f = 0) ∧
    ((∀ i : ℤ, a + 1 ≤ i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) →
      ∀ (M : DerivedCategory (ModuleCat.{v} R))
        (T : Triangle (DerivedCategory (ModuleCat.{v} R))),
        T.obj₁ = K → T.obj₂ = M → T.obj₃ = L →
        T ∈ distTriang (DerivedCategory (ModuleCat.{v} R)) →
        ∃ e : T.obj₂ ≅ T.obj₁ ⊞ T.obj₃,
          T.mor₁ ≫ e.hom = biprod.inl ∧ T.mor₂ = e.hom ≫ biprod.snd) ∧
    ((∀ i : ℤ, a ≤ i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K)) →
      ∀ (M : DerivedCategory (ModuleCat.{v} R))
        (T : Triangle (DerivedCategory (ModuleCat.{v} R))),
        T.obj₁ = K → T.obj₂ = M → T.obj₃ = L →
        T ∈ distTriang (DerivedCategory (ModuleCat.{v} R)) →
        ∀ (e₁ e₂ : T.obj₂ ≅ T.obj₁ ⊞ T.obj₃),
          T.mor₁ ≫ e₁.hom = biprod.inl → T.mor₂ = e₁.hom ≫ biprod.snd →
          T.mor₁ ≫ e₂.hom = biprod.inl → T.mor₂ = e₂.hom ≫ biprod.snd → e₁ = e₂) := by
  obtain ⟨P, hPprojective, hPbounds, ⟨eL⟩⟩ := hL
  have hvan (N : DerivedCategory (ModuleCat.{v} R))
      (hN : ∀ i : ℤ, a ≤ i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj N)) :
      ∀ f : L ⟶ N, f = 0 := by
    let C := (DerivedCategory.Q (C := ModuleCat.{v} R)).objPreimage N
    let eN := (DerivedCategory.Q (C := ModuleCat.{v} R)).objObjPreimageIso N
    have hC (i : ℤ) (hi : a ≤ i) : IsZero (C.homology i) :=
      (hN i hi).of_iso
        (((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i).app C).symm ≪≫
          (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).mapIso eN)
    intro f
    have hz := precise_vanishing (ModuleCat.{v} R) P C a
      ⟨a, b, fun i hi ↦ hPbounds i (Or.inl hi), fun i hi ↦ hPbounds i (Or.inr hi)⟩
      hPprojective (fun i hi ↦ hPbounds i (Or.inl hi)) hC
      (eL.inv ≫ f ≫ eN.inv)
    simpa using congrArg (fun g ↦ eL.hom ≫ g ≫ eN.hom) hz
  refine ⟨hvan K, ?_, ?_⟩
  · intro hK M T h₁ _h₂ h₃ hT
    subst K
    subst L
    apply exists_iso_binaryBiproduct_of_distTriang T hT
    apply hvan _ ?_ T.mor₃
    intro i hi
    exact (hK (i + 1) (by omega)).of_iso
      (((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).shiftIso
        (1 : ℤ) i (i + 1) (by omega)).app T.obj₁)
  · intro hK M T h₁ _h₂ h₃ _hT e₁ e₂ he₁₁ he₁₂ he₂₁ he₂₂
    subst K
    subst L
    have hinl : biprod.inl ≫ e₁.inv = T.mor₁ := by
      rw [← he₁₁]
      simp
    have hleft : biprod.inl ≫ (e₁.inv ≫ e₂.hom) = biprod.inl := by
      rw [← Category.assoc, hinl, he₂₁]
    have hright : (e₁.inv ≫ e₂.hom) ≫ biprod.snd = biprod.snd := by
      rw [Category.assoc, ← he₂₂, he₁₂]
      simp
    have hcomp : e₁.inv ≫ e₂.hom = 𝟙 _ := by
      apply biprod.hom_ext
      · apply biprod.hom_ext'
        · simpa only [Category.assoc, Category.id_comp] using
            congrArg (fun g ↦ g ≫ biprod.fst) hleft
        · simpa using hvan T.obj₁ hK (biprod.inr ≫ (e₁.inv ≫ e₂.hom) ≫ biprod.fst)
      · simpa using hright
    apply Iso.ext
    simpa using (congrArg (fun g ↦ e₁.hom ≫ g) hcomp).symm

end CategoryTheory
