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
  sorry

end CochainComplex
