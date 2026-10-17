/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HypercoverTotalComplex
public import WeilConjectures.Algebra.Homology.ConcreteCohomologyClass

/-!
# Components of the total complex of a hypercover

We describe the components of the differential of the total complex `Tot(U, L)` of
`AlgebraicGeometry.SplitEtaleHypercover.totComplex`, and, in a concrete abelian category, the
elements of `Tot(U, L)` in terms of their components. As an application we prove the
"staircase" reduction: modulo coboundaries, a total cochain whose differential has no
components in positive columns is supported in the column `p = 0`, provided the rows of the
double complex are exact.
-/

@[expose] public section

universe u u'

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.SplitEtaleHypercover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (U : SplitEtaleHypercover X)
  {A : Type u'} [Category.{u + 1} A] [Abelian A]
  (L : CochainComplex (Sheaf X.smallEtaleTopology A) ℕ)

attribute [local instance] Abelian.hasFiniteBiproducts

lemma totι_totD_totπ (a b n : ℕ) (hab : a + b = n) (p r : ℕ) (hpr : p + r = n + 1) :
    U.totι L a b n hab ≫ U.totD L n ≫ U.totπ L p r (n + 1) hpr = U.totEntry L (a, b) (p, r) := by
  rw [totι, totD, totπ, biproduct.ι_matrix_assoc, biproduct.lift_π]

lemma totι_totπ_dite (a b p r n : ℕ) (hab : a + b = n) (hpr : p + r = n) :
    U.totι L a b n hab ≫ U.totπ L p r n hpr =
      if hh : (a, b) = (p, r) then eqToHom (by simp only [Prod.mk.injEq] at hh; rw [hh.1, hh.2])
      else 0 := by
  rw [totπ, totι_π]

lemma totD_totπ_zero (r n : ℕ) (h : r = n) :
    U.totD L n ≫ U.totπ L 0 (r + 1) (n + 1) (by omega) =
      U.totπ L 0 r n (by omega) ≫ U.dVert L 0 r := by
  subst h
  apply totObj_hom_ext
  intro a b hab
  rw [totι_totD_totπ, ← Category.assoc, totι_totπ_dite, totEntry]
  by_cases h₁ : a = 0
  · subst h₁
    obtain rfl : b = r := by omega
    simp
  · rw [dif_neg (by simp only [Prod.mk.injEq]; omega),
      dif_neg (by simp only [Prod.mk.injEq]; omega),
      dif_neg (by simp only [Prod.mk.injEq]; omega)]
    simp

lemma totD_totπ_succ_zero (p n : ℕ) (h : p = n) :
    U.totD L n ≫ U.totπ L (p + 1) 0 (n + 1) (by omega) =
      U.totπ L p 0 n (by omega) ≫ U.dHor L p 0 := by
  subst h
  apply totObj_hom_ext
  intro a b hab
  rw [totι_totD_totπ, ← Category.assoc, totι_totπ_dite, totEntry]
  by_cases h₁ : a = p
  · subst h₁
    obtain rfl : b = 0 := by omega
    simp
  · rw [dif_neg (by simp only [Prod.mk.injEq]; omega),
      dif_neg (by simp only [Prod.mk.injEq]; omega),
      dif_neg (by simp only [Prod.mk.injEq]; omega)]
    simp

lemma totD_totπ_succ_succ (p s n : ℕ) (h : p + s + 1 = n) :
    U.totD L n ≫ U.totπ L (p + 1) (s + 1) (n + 1) (by omega) =
      U.totπ L p (s + 1) n (by omega) ≫ U.dHor L p (s + 1) +
        ((-1 : ℤ) ^ (p + 1)) • U.totπ L (p + 1) s n (by omega) ≫ U.dVert L (p + 1) s := by
  apply totObj_hom_ext
  intro a b hab
  rw [totι_totD_totπ, Preadditive.comp_add, Preadditive.comp_zsmul, ← Category.assoc,
    ← Category.assoc, totι_totπ_dite, totι_totπ_dite, totEntry]
  by_cases h₁ : a = p
  · subst h₁
    obtain rfl : b = s + 1 := by omega
    rw [dif_pos rfl, dif_neg (by simp), dif_pos rfl, dif_neg (by simp)]
    simp
  · by_cases h₂ : a = p + 1
    · subst h₂
      obtain rfl : b = s := by omega
      rw [dif_neg (by simp), dif_pos rfl, dif_neg (by simp), dif_pos rfl]
      simp
    · rw [dif_neg (by simp only [Prod.mk.injEq]; omega),
        dif_neg (by simp only [Prod.mk.injEq]; omega),
        dif_neg (by simp only [Prod.mk.injEq]; omega),
        dif_neg (by simp only [Prod.mk.injEq]; omega)]
      simp

end AlgebraicGeometry.SplitEtaleHypercover
