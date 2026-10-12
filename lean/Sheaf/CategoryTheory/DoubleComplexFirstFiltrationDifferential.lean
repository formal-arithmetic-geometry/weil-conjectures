/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import Sheaf.CategoryTheory.DoubleComplexTotal

/-! # The first total filtration is a subcomplex

Source: Stacks Project, Homology, Tag 012Z
(blueprint: lem-weil-pbc-total-first-filtration-differential).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

private theorem factors_units_smul
    {C : Type u} [Category.{v} C] [Abelian C] {X Y : C}
    (Q : Subobject Y) (f : X ⟶ Y) (h : Q.Factors f) (z : ℤˣ) :
    Q.Factors (z • f) := by
  rw [Subobject.factors_iff]
  exact ⟨z • Q.factorThru f h, by simp [Linear.units_smul_comp]⟩

/-- The differential preserves the first finite image-sum filtration.
Source: Stacks Project, Homology, Tag 012Z
(blueprint: lem-weil-pbc-total-first-filtration-differential).

Proof: for a diagonal summand with r ≤ p ≤ n, the horizontal differential lands
in the summand (p+1,n-p) and the signed vertical differential in (p,n-p+1).
Both first degrees lie in [r,n+1]. Hence both composites factor through the
corresponding target images and their finite supremum. Addition and multiplication
by the sign preserve this factorization. Pulling the target step back along the
total differential shows that every source image, and thus their finite supremum,
lies in that pullback. Its universal property gives the required map. No quadrant
hypothesis is needed for these particular finite image-sum steps. -/
theorem firstFiltration_differential
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r n : ℤ) :
    ∃ f : ((K.firstFiltration n).step r : C) ⟶
      ((K.firstFiltration (n + 1)).step r : C),
      f ≫ ((K.firstFiltration (n + 1)).step r).arrow =
        ((K.firstFiltration n).step r).arrow ≫
          (K.total (ComplexShape.up ℤ)).d n (n + 1) := by
  classical
  let g := (K.total (ComplexShape.up ℤ)).d n (n + 1)
  let Q := (K.firstFiltration (n + 1)).step r
  let P := (Subobject.pullback g).obj Q
  have h : (K.firstFiltration n).step r ≤ P := by
    change (Finset.Icc r n).sup _ ≤ P
    apply Finset.sup_le
    intro i hi
    let a := K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n
    have h₁ : Q.Factors ((K.d i (i + 1)).f (n - i) ≫
        K.ιTotalOrZero (ComplexShape.up ℤ) (i + 1) (n - i) (n + 1)) := by
      have heq : n - i = (n + 1) - (i + 1) := by omega
      rw [heq]
      change Subobject.Factors ((Finset.Icc r (n + 1)).sup
        (fun j ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ) j ((n + 1) - j)
          (n + 1)))) _
      apply Subobject.finset_sup_factors
      exact ⟨i + 1, Finset.mem_Icc.mpr (by rcases Finset.mem_Icc.mp hi with ⟨_, _⟩; omega),
        imageSubobject_factors_comp_self _ _⟩
    have h₂ : Q.Factors ((K.X i).d (n - i) (n - i + 1) ≫
        K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i + 1) (n + 1)) := by
      have heq : n - i + 1 = (n + 1) - i := by omega
      rw [heq]
      change Subobject.Factors ((Finset.Icc r (n + 1)).sup
        (fun j ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ) j ((n + 1) - j)
          (n + 1)))) _
      apply Subobject.finset_sup_factors
      exact ⟨i, Finset.mem_Icc.mpr (by rcases Finset.mem_Icc.mp hi with ⟨_, _⟩; omega),
        imageSubobject_factors_comp_self _ _⟩
    have hQ : Q.Factors (a ≫ g) := by
      dsimp [a, g]
      rw [K.ιTotalOrZero_eq _ _ _ _ (by simp), total_d, Preadditive.comp_add,
        ι_D₁, ι_D₂, K.d₁_eq' _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
        K.d₂_eq' _ i (show (ComplexShape.up ℤ).Rel (n - i) (n - i + 1) by simp)]
      exact Subobject.factors_add _ _ (factors_units_smul Q _ h₁ _)
        (factors_units_smul Q _ h₂ _)
    have hP : P.Factors a := pullback_factors g Q a hQ
    exact imageSubobject_le a (P.factorThru a hP) (P.factorThru_arrow a hP)
  have hP := Subobject.factors_of_le ((K.firstFiltration n).step r).arrow h
    (Subobject.factors_self _)
  have hQ := (pullback_factors_iff g Q _).mp hP
  exact ⟨Q.factorThru _ hQ, Q.factorThru_arrow _ hQ⟩

end HomologicalComplex₂
