/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

/-! # Horizontal comparison homotopy for Cartan--Eilenberg rows

Source: Stacks Project, derived.tex, Tag 015I and Tag 013P(2)
(blueprint: lem-sp-ce-horizontal-lift).

As in `CategoryTheory.exists_cartanEilenberg_resolution`, vertical indices are natural,
augmentations are bicomplex morphisms from the vertical single-degree complex, and
exact augmented rows are expressed by quasi-isomorphisms from that complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v

/-- Columnwise horizontal comparison homotopy for Cartan--Eilenberg resolutions.
Source: Stacks Project, derived.tex, Tag 015I; Tag 013P(2) for the comparison lift;
Weibel, Homological Algebra, Lemma 5.7.10 (blueprint: lem-sp-ce-horizontal-lift).

Proof:
1. For each p, augmented column exactness makes eI.f p a degreewise monic
   quasi-isomorphism from K^p[0] to I^{p,bullet}. The map epsilon_J^{p-1} s^p
   into the bounded-below injective column J^{p-1,bullet} extends to a column
   morphism s1 p by lem-weil-pbc-lift-along-injective-quasi-iso (Tag 013P(2)).
   For p <= 0 the target column is zero by first-quadrant vanishing; the zero
   map satisfies the augmentation equation without assuming L vanishes there.
2. Set R^p = delta^p - s1^p d_J^{p-1} - d_I^p s1^{p+1}.
   Each summand is a column morphism, so R commutes with vertical differentials.
   Commutation of the augmentations with horizontal differentials identifies
   epsilon_I^p R^{p,0} with epsilon_J^p times
   w^p - s^p d_L^{p-1} - d_K^p s^{p+1}, which vanishes by hhom.
   This gives the residual identity and its vanishing on the augmentation.
-/
theorem horizontal_comparison_lift
    (A : Type u) [Category.{v} A] [Abelian A]
    (K L : CochainComplex A ℤ)
    (I J : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (eI : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶ I)
    (eJ : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶ J)
    (δ : I ⟶ J)
    (hFirstI : ∀ p : ℤ, p < 0 → IsZero (I.X p))
    (hFirstJ : ∀ p : ℤ, p < 0 → IsZero (J.X p))
    (hExactI : ∀ p : ℤ, QuasiIso (eI.f p))
    (hInjectiveJ : ∀ (p : ℤ) (q : ℕ), Injective ((J.X p).X q))
    (hRowsI : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eI p) ∧
      QuasiIso
        (image.map (Arrow.homMk' (eI.f (p - 1)) (eI.f p) (eI.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eI p))
    (hRowsJ : ∀ p : ℤ,
      QuasiIso (HomologicalComplex.cyclesMap eJ p) ∧
      QuasiIso
        (image.map (Arrow.homMk' (eJ.f (p - 1)) (eJ.f p) (eJ.comm (p - 1) p))) ∧
      QuasiIso (HomologicalComplex.homologyMap eJ p))
    (hRowInjectiveJ : ∀ (p : ℤ) (q : ℕ),
      Injective ((J.cycles p).X q) ∧
      Injective ((image (J.d (p - 1) p)).X q) ∧
      Injective ((J.homology p).X q))
    (w : K ⟶ L)
    (s : ∀ p : ℤ, K.X p ⟶ L.X (p - 1))
    (hhom : ∀ p : ℤ,
      w.f p = s p ≫ L.d (p - 1) p +
        K.d p (p + 1) ≫ s (p + 1) ≫ (L.XIsoOfEq (Int.add_sub_cancel p 1)).hom)
    (haug : ∀ p : ℤ, (eI.f p).f 0 ≫ (δ.f p).f 0 = w.f p ≫ (eJ.f p).f 0) :
    ∃ (s₁ : ∀ p : ℤ, I.X p ⟶ J.X (p - 1))
      (R : ∀ p : ℤ, I.X p ⟶ J.X p),
      (∀ p : ℤ, (eI.f p).f 0 ≫ (s₁ p).f 0 = s p ≫ (eJ.f (p - 1)).f 0) ∧
      (∀ p : ℤ, R p = δ.f p - s₁ p ≫ J.d (p - 1) p -
        I.d p (p + 1) ≫ s₁ (p + 1) ≫ (J.XIsoOfEq (Int.add_sub_cancel p 1)).hom) ∧
      (∀ p : ℤ, (eI.f p).f 0 ≫ (R p).f 0 = 0) := by
  sorry

end CategoryTheory
