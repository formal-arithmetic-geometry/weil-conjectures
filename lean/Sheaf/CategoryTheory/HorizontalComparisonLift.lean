/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

import WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution

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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Extend a closed augmentation map to a target complex of injectives.
The quasi-isomorphism identifies the augmentation with the degree-zero kernel,
and makes the source exact in positive degrees. Injectivity extends the map in
degree zero, and `Exact.descToInjective` extends each succeeding component.
Source: Stacks Tag 013P(2); Mathlib's `InjectiveResolution.desc` recursion. -/
private theorem lift_from_exact_augmentation
    {C : Type*} [Category* C] [Abelian C] {X : C}
    {M N : CochainComplex C ℕ} (e : (CochainComplex.single₀ C).obj X ⟶ M)
    [QuasiIso e] [∀ n, Injective (N.X n)]
    (f : X ⟶ N.X 0) (hf : f ≫ N.d 0 1 = 0) :
    ∃ α : M ⟶ N, e.f 0 ≫ α.f 0 = f := by
  have hexact := CochainComplex.exact₀_of_quasiIso_single₀ e
  let a₀ : M.X 0 ⟶ N.X 0 := Injective.factorThru f (e.f 0)
  have ha₀ : e.f 0 ≫ a₀ = f := Injective.comp_factorThru _ _
  let a₁ := hexact.descToInjective (a₀ ≫ N.d 0 1) (by
    rw [← Category.assoc, ha₀, hf])
  have ha₁ : M.d 0 1 ≫ a₁ = a₀ ≫ N.d 0 1 := hexact.comp_descToInjective _ _
  let α := CochainComplex.mkHom M N a₀ a₁ ha₁.symm
    (fun n ⟨a, b, h⟩ ↦
      ⟨(CochainComplex.exact_succ_of_quasiIso_single₀ e n).descToInjective
          (b ≫ N.d (n + 1) (n + 2)) (by
          rw [← Category.assoc, ← h, Category.assoc, N.d_comp_d, comp_zero]),
        ((CochainComplex.exact_succ_of_quasiIso_single₀ e n).comp_descToInjective _ _).symm⟩)
  exact ⟨α, ha₀⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
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
  classical
  have hs (p : ℤ) : ∃ t : I.X p ⟶ J.X (p - 1),
      (eI.f p).f 0 ≫ t.f 0 = s p ≫ (eJ.f (p - 1)).f 0 := by
    have : QuasiIso (eI.f p) := hExactI p
    let : ∀ q, Injective ((J.X (p - 1)).X q) := hInjectiveJ (p - 1)
    apply lift_from_exact_augmentation (eI.f p) (s p ≫ (eJ.f (p - 1)).f 0)
    have hz : (eJ.f (p - 1)).f 0 ≫ (J.X (p - 1)).d 0 1 = 0 :=
      ((CochainComplex.fromSingle₀Equiv (J.X (p - 1)) (L.X (p - 1)))
        (eJ.f (p - 1))).property
    rw [Category.assoc, hz, comp_zero]
  choose s₁ hs₁ using hs
  let R (p : ℤ) : I.X p ⟶ J.X p := δ.f p - s₁ p ≫ J.d (p - 1) p -
    I.d p (p + 1) ≫ s₁ (p + 1) ≫ (J.XIsoOfEq (Int.add_sub_cancel p 1)).hom
  refine ⟨s₁, R, hs₁, fun _ ↦ rfl, ?_⟩
  intro p
  have heI (a b : ℤ) :
      (eI.f a).f 0 ≫ (I.d a b).f 0 = K.d a b ≫ (eI.f b).f 0 := by
    simp
  have heJ (a b : ℤ) :
      (eJ.f a).f 0 ≫ (J.d a b).f 0 = L.d a b ≫ (eJ.f b).f 0 := by
    simp
  have heq :
      (eJ.f (p + 1 - 1)).f 0 ≫ ((J.XIsoOfEq (Int.add_sub_cancel p 1)).hom).f 0 =
        (L.XIsoOfEq (Int.add_sub_cancel p 1)).hom ≫ (eJ.f p).f 0 := by
    have hn (a b : ℤ) (h : a = b) :
        (eJ.f a).f 0 ≫ ((J.XIsoOfEq h).hom).f 0 =
          (L.XIsoOfEq h).hom ≫ (eJ.f b).f 0 := by
      subst b
      simp
    exact hn _ _ _
  have h₁ : (eI.f p).f 0 ≫ (s₁ p ≫ J.d (p - 1) p).f 0 =
      (s p ≫ L.d (p - 1) p) ≫ (eJ.f p).f 0 := by
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [reassoc_of% hs₁ p, heJ]
  have h₂ : (eI.f p).f 0 ≫
      (I.d p (p + 1) ≫ s₁ (p + 1) ≫
        (J.XIsoOfEq (Int.add_sub_cancel p 1)).hom).f 0 =
      (K.d p (p + 1) ≫ s (p + 1) ≫
        (L.XIsoOfEq (Int.add_sub_cancel p 1)).hom) ≫ (eJ.f p).f 0 := by
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [reassoc_of% heI p (p + 1), reassoc_of% hs₁ (p + 1), heq]
  dsimp only [R]
  simp only [HomologicalComplex.sub_f_apply, Preadditive.comp_sub]
  rw [haug p, h₁, h₂, ← Preadditive.sub_comp, ← Preadditive.sub_comp, hhom p]
  simp

end CategoryTheory
