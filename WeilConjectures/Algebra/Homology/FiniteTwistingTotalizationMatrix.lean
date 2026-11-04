/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationData
public import WeilConjectures.Mathlib.Data.Fintype.BigOperators

/-! # Matrix part of a finite twisting totalization

The matrix theorem records only the direct-sum complex, its coordinates, the
component formula, and the square-zero calculation.  The tail filtration and
the graded quotients are deliberately separate data in
`FiniteTwistingTotalizationFiltration`.
-/

/- The matrix construction is an existing dependency of the finite totalization structure. -/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})
variable {R} {a b : ℤ}

set_option linter.unusedVariables false in
/-- The category of module sheaves in which a finite twisting family lives. -/
abbrev finiteTwistingModule (D : FiniteTwistingFamily R a b) :=
  ringedSiteModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)

/-- The data supplied by the upper-triangular matrix calculation, before adding
the tail filtration. -/
structure FiniteTwistingMatrixData (D : FiniteTwistingFamily R a b) where
  /-- The total complex. -/
  P : CochainComplex (finiteTwistingModule D) ℤ
  /-- Each term is identified with the finite direct sum of the given terms. -/
  coordinates : ∀ n : ℤ, P.X n ≅
    ⨁ fun p : ↥(Finset.Icc a b) ↦ (D.G p).X n
  /-- On each summand, the differential is the diagonal differential plus the strictly
  upper triangular twisting components. -/
  differential : ∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
    biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p ≫
        (coordinates n).inv ≫ P.d n (n + 1) =
      (D.G p).d n (n + 1) ≫
          biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X (n + 1)) p ≫
            (coordinates (n + 1)).inv +
        ∑ q : {q : ↥(Finset.Icc a b) // p.val < q.val},
          D.τ p q.val q.property n ≫
            biproduct.ι (fun t : ↥(Finset.Icc a b) ↦ (D.G t).X (n + 1)) q.val ≫
              (coordinates (n + 1)).inv
  /-- The differential squares to zero. -/
  square : ∀ n : ℤ, P.d n (n + 1) ≫ P.d (n + 1) (n + 1 + 1) = 0

section Helpers

variable {V : Type*} [Category V] [Preadditive V]

/-- Projecting a sum of maps into summands indexed by a subtype onto one summand. -/
private lemma biproduct_sum_subtype_comp_ι_comp_π {ι : Type*}
    {F : ι → V} [HasBiproduct F] {X : V} (P : ι → Prop) [DecidablePred P]
    [Fintype (Subtype P)]
    (f : ∀ q : Subtype P, X ⟶ F q.val) (r : ι) :
    ∑ q : Subtype P, f q ≫ biproduct.ι F q.val ≫ biproduct.π F r =
      if h : P r then f ⟨r, h⟩ else 0 := by
  by_cases h : P r
  · rw [dif_pos h, Fintype.sum_eq_single ⟨r, h⟩, biproduct.ι_π_self, Category.comp_id]
    intro q hq
    rw [biproduct.ι_π_ne _ fun e ↦ hq (Subtype.ext e), comp_zero]
  · rw [dif_neg h]
    exact Fintype.sum_eq_zero _ fun q ↦ by
      rw [biproduct.ι_π_ne _ fun e : q.val = r ↦ h (e ▸ q.2), comp_zero]

/-- Two-factor variant of `biproduct_sum_subtype_comp_ι_comp_π`. -/
private lemma biproduct_sum_subtype_comp_comp_ι_comp_π {ι : Type*}
    {F : ι → V} [HasBiproduct F] {X : V} (P : ι → Prop) [DecidablePred P]
    [Fintype (Subtype P)]
    {Y : ι → V} (f : ∀ q : Subtype P, X ⟶ Y q.val) (g : ∀ q : Subtype P, Y q.val ⟶ F q.val)
    (r : ι) :
    ∑ q : Subtype P, f q ≫ g q ≫ biproduct.ι F q.val ≫ biproduct.π F r =
      if h : P r then f ⟨r, h⟩ ≫ g ⟨r, h⟩ else 0 := by
  simpa only [Category.assoc] using
    biproduct_sum_subtype_comp_ι_comp_π P (fun q ↦ f q ≫ g q) r

end Helpers

/-- The upper triangular differential on the direct sum of the terms of a finite
twisting family: the diagonal differential plus the twisting components. -/
noncomputable def finiteTwistingMatrixD (D : FiniteTwistingFamily R a b) (n : ℤ) :
    (⨁ fun p : ↥(Finset.Icc a b) ↦ (D.G p).X n) ⟶
      ⨁ fun p : ↥(Finset.Icc a b) ↦ (D.G p).X (n + 1) :=
  biproduct.desc fun p ↦
    (D.G p).d n (n + 1) ≫ biproduct.ι (fun t : ↥(Finset.Icc a b) ↦ (D.G t).X (n + 1)) p +
    ∑ q : {q : ↥(Finset.Icc a b) // p.val < q.val},
      D.τ p q.val q.property n ≫
        biproduct.ι (fun t : ↥(Finset.Icc a b) ↦ (D.G t).X (n + 1)) q.val

omit [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Injection of a summand followed by `finiteTwistingMatrixD`. -/
@[reassoc]
lemma ι_finiteTwistingMatrixD (D : FiniteTwistingFamily R a b) (p : ↥(Finset.Icc a b))
    (n : ℤ) :
    biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p ≫ finiteTwistingMatrixD D n =
      (D.G p).d n (n + 1) ≫
          biproduct.ι (fun t : ↥(Finset.Icc a b) ↦ (D.G t).X (n + 1)) p +
        ∑ q : {q : ↥(Finset.Icc a b) // p.val < q.val},
          D.τ p q.val q.property n ≫
            biproduct.ι (fun t : ↥(Finset.Icc a b) ↦ (D.G t).X (n + 1)) q.val :=
  biproduct.ι_desc _ _

omit [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The matrix entries of `finiteTwistingMatrixD`. -/
lemma ι_finiteTwistingMatrixD_π (D : FiniteTwistingFamily R a b) (p r : ↥(Finset.Icc a b))
    (n : ℤ) :
    biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p ≫ finiteTwistingMatrixD D n ≫
        biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X (n + 1)) r =
      (D.G p).d n (n + 1) ≫
          biproduct.ι (fun t : ↥(Finset.Icc a b) ↦ (D.G t).X (n + 1)) p ≫
          biproduct.π (fun t : ↥(Finset.Icc a b) ↦ (D.G t).X (n + 1)) r +
        if h : p.val < r.val then D.τ p r h n else 0 := by
  rw [ι_finiteTwistingMatrixD_assoc, Preadditive.add_comp, Preadditive.sum_comp,
    Category.assoc]
  simp only [Category.assoc]
  rw [biproduct_sum_subtype_comp_ι_comp_π
    (F := fun t : ↥(Finset.Icc a b) ↦ (D.G t).X (n + 1))
    (fun q : ↥(Finset.Icc a b) ↦ p.val < q.val) (fun q ↦ D.τ p q.val q.property n) r]

omit [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The upper triangular differential squares to zero, by `d_comp_d` on the diagonal
and the Maurer--Cartan equations above it. -/
lemma finiteTwistingMatrixD_comp (D : FiniteTwistingFamily R a b) (n : ℤ) :
    finiteTwistingMatrixD D n ≫ finiteTwistingMatrixD D (n + 1) = 0 := by
  refine biproduct.hom_ext' _ _ fun p ↦ biproduct.hom_ext _ _ fun r ↦ ?_
  rw [comp_zero, zero_comp, Category.assoc, Category.assoc, ι_finiteTwistingMatrixD_assoc,
    Preadditive.add_comp, Preadditive.sum_comp]
  simp only [Category.assoc, ι_finiteTwistingMatrixD_π, Preadditive.comp_add,
    Finset.sum_add_distrib, HomologicalComplex.d_comp_d_assoc, zero_comp, zero_add]
  rw [biproduct_sum_subtype_comp_comp_ι_comp_π
    (F := fun t : ↥(Finset.Icc a b) ↦ (D.G t).X (n + 1 + 1))
    (Y := fun t : ↥(Finset.Icc a b) ↦ (D.G t).X (n + 1))
    (fun q : ↥(Finset.Icc a b) ↦ p.val < q.val)
    (fun q ↦ D.τ p q.val q.property n) (fun q ↦ (D.G q.val).d (n + 1) (n + 1 + 1)) r]
  by_cases h : p.val < r.val
  · have hsum : ∑ q : {q : ↥(Finset.Icc a b) // p.val < q.val},
        D.τ p q.val q.property n ≫
          (if h' : q.val.val < r.val then D.τ q.val r h' (n + 1) else 0) =
        ∑ s : {s : ↥(Finset.Icc a b) // p.val < s.val ∧ s.val < r.val},
          D.τ p s.val s.property.1 n ≫ D.τ s.val r s.property.2 (n + 1) := by
      rw [Fintype.sum_subtype_eq_sum_dite (fun q : ↥(Finset.Icc a b) ↦ p.val < q.val),
        Fintype.sum_subtype_eq_sum_dite
          (fun s : ↥(Finset.Icc a b) ↦ p.val < s.val ∧ s.val < r.val)]
      refine Fintype.sum_congr _ _ fun q ↦ ?_
      by_cases h1 : p.val < q.val
      · by_cases h2 : q.val < r.val
        · rw [dif_pos h1, dif_pos h2, dif_pos ⟨h1, h2⟩]
        · rw [dif_pos h1, dif_neg h2, dif_neg fun h3 ↦ h2 h3.2, comp_zero]
      · rw [dif_neg h1, dif_neg fun h3 ↦ h1 h3.1]
    simp only [dif_pos h]
    rw [hsum]
    refine Eq.trans ?_ (D.maurerCartan p r h n)
    abel
  · simp only [dif_neg h, comp_zero, zero_add]
    refine Finset.sum_eq_zero fun q _ ↦ ?_
    rw [dif_neg fun h' ↦ h (q.property.trans h'), comp_zero]

omit [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The triangular biproduct construction.  The proof defines the differential by
`biproduct.desc`; injection followed by the differential is the diagonal
differential plus the strictly upper triangular twisting sum.  Applying a
second differential and then every biproduct projection gives zero on the
diagonal by `CochainComplex.d_comp_d`, and gives exactly
`D.maurerCartan` in every entry above the diagonal.  Biproduct hom extensionality
then proves the square-zero field.
(blueprint: lem-trf-finite-filtered-totalization-matrix) -/
theorem exists_finiteTwistingMatrixData
    (a b : ℤ) (D : FiniteTwistingFamily R a b) :
    Nonempty (FiniteTwistingMatrixData D) :=
  ⟨{P := CochainComplex.of (fun n ↦ ⨁ fun p : ↥(Finset.Icc a b) ↦ (D.G p).X n)
        (finiteTwistingMatrixD D) (finiteTwistingMatrixD_comp D)
    coordinates _ := Iso.refl _
    differential p n := by
      simp only [Iso.refl_inv, Category.id_comp, Category.comp_id, CochainComplex.of_d]
      exact ι_finiteTwistingMatrixD D p n
    square _ := HomologicalComplex.d_comp_d _ _ _ _ }⟩

end CochainComplex
