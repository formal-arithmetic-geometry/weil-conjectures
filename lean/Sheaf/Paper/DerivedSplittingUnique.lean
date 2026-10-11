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
  sorry

end CategoryTheory
