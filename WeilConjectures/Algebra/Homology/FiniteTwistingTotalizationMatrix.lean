/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationData

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

abbrev finiteTwistingModule (D : FiniteTwistingFamily R a b) :=
  ringedSiteModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)

/-- The data supplied by the upper-triangular matrix calculation, before adding
the tail filtration. -/
structure FiniteTwistingMatrixData (D : FiniteTwistingFamily R a b) where
  P : CochainComplex (finiteTwistingModule D) ℤ
  coordinates : ∀ n : ℤ, P.X n ≅
    ⨁ fun p : ↥(Finset.Icc a b) ↦ (D.G p).X n
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
  square : ∀ n : ℤ, P.d n (n + 1) ≫ P.d (n + 1) (n + 1 + 1) = 0

/-- The degree `n` upper-triangular matrix of a finite twisting family: on the summand of
weight `p` it is the differential of `D.G p` plus the twisting maps to all higher weights. -/
noncomputable def finiteTwistingMatrix (D : FiniteTwistingFamily R a b) (n : ℤ) :
    (⨁ fun p : ↥(Finset.Icc a b) ↦ (D.G p).X n) ⟶
      ⨁ fun p : ↥(Finset.Icc a b) ↦ (D.G p).X (n + 1) :=
  biproduct.desc fun p ↦
    (D.G p).d n (n + 1) ≫ biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X (n + 1)) p +
      ∑ q : {q : ↥(Finset.Icc a b) // p.val < q.val},
        D.τ p q.val q.property n ≫
          biproduct.ι (fun t : ↥(Finset.Icc a b) ↦ (D.G t).X (n + 1)) q.val

omit [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The summand of weight `p` of the twisting matrix. -/
@[reassoc]
lemma ι_finiteTwistingMatrix (D : FiniteTwistingFamily R a b) (n : ℤ)
    (p : ↥(Finset.Icc a b)) :
    biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p ≫ finiteTwistingMatrix D n =
      (D.G p).d n (n + 1) ≫ biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X (n + 1)) p +
        ∑ q : {q : ↥(Finset.Icc a b) // p.val < q.val},
          D.τ p q.val q.property n ≫
            biproduct.ι (fun t : ↥(Finset.Icc a b) ↦ (D.G t).X (n + 1)) q.val :=
  biproduct.ι_desc _ _

omit [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The `(p, t)` entry of the twisting matrix. -/
lemma ι_finiteTwistingMatrix_π (D : FiniteTwistingFamily R a b) (n : ℤ)
    (p t : ↥(Finset.Icc a b)) :
    biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p ≫ finiteTwistingMatrix D n ≫
        biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X (n + 1)) t =
      (if h : p = t then (D.G p).d n (n + 1) ≫ eqToHom (by rw [h]) else 0) +
        if h : p.val < t.val then D.τ p t h n else 0 := by
  classical
  rw [ι_finiteTwistingMatrix_assoc, Preadditive.add_comp, Category.assoc, biproduct.ι_π,
    Preadditive.sum_comp]
  congr 1
  · split_ifs <;> simp
  · split_ifs with h
    · rw [Finset.sum_eq_single ⟨t, h⟩]
      · simp
      · intro q _ hq
        rw [Category.assoc, biproduct.ι_π_ne _ (fun e ↦ hq (Subtype.ext e)), comp_zero]
      · simp
    · refine Finset.sum_eq_zero fun q _ ↦ ?_
      rw [Category.assoc, biproduct.ι_π_ne _ (fun e ↦ h (by rw [← e]; exact q.property)),
        comp_zero]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Summing the products of twisting maps through intermediate weights below `t`. -/
lemma sum_finiteTwisting_τ_comp_τ (D : FiniteTwistingFamily R a b) (n : ℤ)
    (p t : ↥(Finset.Icc a b)) :
    ∑ q : {q : ↥(Finset.Icc a b) // p.val < q.val},
        (D.τ p q.val q.property n ≫
          if h : q.val.val < t.val then D.τ q.val t h (n + 1) else 0) =
      ∑ r : {r : ↥(Finset.Icc a b) // p.val < r.val ∧ r.val < t.val},
        D.τ p r.val r.property.1 n ≫ D.τ r.val t r.property.2 (n + 1) := by
  symm
  refine Fintype.sum_of_injective (fun r ↦ ⟨r.val, r.property.1⟩)
    (fun r s h ↦ Subtype.ext (by simpa using congrArg Subtype.val h)) _ _ ?_ ?_
  · intro q hq
    rw [dif_neg (fun h ↦ hq ⟨⟨q.val, q.property, h⟩, rfl⟩), comp_zero]
  · intro r
    rw [dif_pos r.property.2]

omit [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The twisting matrix squares to zero, by `d_comp_d` on the diagonal and the
Maurer--Cartan equation above it. -/
lemma finiteTwistingMatrix_comp (D : FiniteTwistingFamily R a b) (n : ℤ) :
    finiteTwistingMatrix D n ≫ finiteTwistingMatrix D (n + 1) = 0 := by
  classical
  refine biproduct.hom_ext' _ _ fun p ↦ biproduct.hom_ext _ _ fun t ↦ ?_
  rw [comp_zero, zero_comp, ι_finiteTwistingMatrix_assoc]
  simp_rw [Preadditive.add_comp, Preadditive.sum_comp, Category.assoc,
    ι_finiteTwistingMatrix_π, Preadditive.comp_add]
  rw [Finset.sum_add_distrib, sum_finiteTwisting_τ_comp_τ]
  by_cases hpt : p = t
  · subst hpt
    simp only [dite_true, dif_neg (lt_irrefl p.val), comp_zero, add_zero,
      eqToHom_refl, Category.comp_id, HomologicalComplex.d_comp_d, zero_add]
    refine (congrArg₂ (· + ·) (Finset.sum_eq_zero ?_) (Finset.sum_eq_zero ?_)).trans
      (add_zero 0)
    · refine fun q _ ↦ ?_
      rw [dif_neg (fun h ↦ (lt_irrefl p.val) (by simpa [h] using q.property)), comp_zero]
    · exact fun r _ ↦ absurd (r.property.1.trans r.property.2) (lt_irrefl _)
  simp only [dif_neg hpt, comp_zero, zero_add]
  by_cases hlt : p.val < t.val
  · simp only [dif_pos hlt]
    rw [Finset.sum_eq_single ⟨t, hlt⟩]
    · simp only [dite_true, eqToHom_refl, Category.comp_id]
      exact (add_left_comm _ _ _).trans ((add_assoc _ _ _).symm.trans (D.maurerCartan p t hlt n))
    · intro q _ hq
      rw [dif_neg (fun h ↦ hq (Subtype.ext h)), comp_zero]
    · simp
  · simp only [dif_neg hlt, comp_zero, zero_add]
    refine (congrArg₂ (· + ·) (Finset.sum_eq_zero ?_) (Finset.sum_eq_zero ?_)).trans
      (add_zero 0)
    · refine fun q _ ↦ ?_
      rw [dif_neg (fun h ↦ hlt (by simpa [h] using q.property)), comp_zero]
    · exact fun r _ ↦ absurd (r.property.1.trans r.property.2) hlt

/-- The triangular biproduct construction.  The proof defines the differential by
`biproduct.desc`; injection followed by the differential is the diagonal
differential plus the strictly upper triangular twisting sum.  Applying a
second differential and then every biproduct projection gives zero on the
diagonal by `CochainComplex.d_comp_d`, and gives exactly
`D.maurerCartan` in every entry above the diagonal.  Biproduct hom extensionality
then proves the square-zero field.
(blueprint: lem-trf-finite-filtered-totalization-matrix) -/
theorem exists_finiteTwistingMatrixData
    (a b : ℤ) (hab : a ≤ b) (D : FiniteTwistingFamily R a b) :
    ∃ X : FiniteTwistingMatrixData D, True := by
  refine ⟨{ P := CochainComplex.of (fun n ↦ ⨁ fun p : ↥(Finset.Icc a b) ↦ (D.G p).X n)
              (finiteTwistingMatrix D) (finiteTwistingMatrix_comp D)
            coordinates := fun n ↦ Iso.refl _
            differential := fun p n ↦ ?_
            square := fun n ↦ ?_ }, trivial⟩
  · simp only [Iso.refl_inv, Category.id_comp, Category.comp_id, CochainComplex.of_d,
      ι_finiteTwistingMatrix]
  · simp only [CochainComplex.of_d]
    exact finiteTwistingMatrix_comp D n

end CochainComplex
