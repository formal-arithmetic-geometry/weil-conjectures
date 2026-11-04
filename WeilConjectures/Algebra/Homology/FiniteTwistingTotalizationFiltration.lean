/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationTail

/-! # Tail data for a finite twisting totalization

This record contains the decreasing tail filtration and its canonical coordinate,
splitting, and graded quotient data.  It is separated from the matrix calculation
so that each missing part is a proper subproblem of the final realization theorem.
-/

/- The filtration construction is an existing dependency of the finite totalization structure. -/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})
variable {R} {a b : ℤ}

/-- The filtration data required to turn matrix data into a realization record. -/
structure FiniteTwistingFiltrationData
    (D : FiniteTwistingFamily R a b) (X : FiniteTwistingMatrixData D) where
  /-- The decreasing filtration of the total complex by tails. -/
  F : DecreasingFiltration X.P
  /-- The identifications of the graded pieces with the given complexes. -/
  gradedIso : ∀ p : ↥(Finset.Icc a b), F.gradedPiece p.val ≅ D.G p
  /-- Finiteness in the dependency's existing sense. -/
  finite : F.IsFinite
  /-- The full tail. -/
  bottomWeight : F.step a = ⊤
  /-- The empty tail. -/
  topWeight : F.step (b + 1) = ⊥
  /-- Term coordinates for every tail, including empty tails. -/
  tailCoordinates : ∀ r n : ℤ,
    ((F.step r : CochainComplex _ ℤ).X n) ≅
      ⨁ fun p : {p : ↥(Finset.Icc a b) // r ≤ p.val} ↦ (D.G p.val).X n
  /-- Each tail inclusion is the inclusion of precisely the prescribed summands. -/
  tailInclusion : ∀ r n : ℤ,
    (tailCoordinates r n).inv ≫ (F.step r).arrow.f n =
      biproduct.desc (fun p : {p : ↥(Finset.Icc a b) // r ≤ p.val} ↦
        biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p.val ≫
          (X.coordinates n).inv)
  /-- Splitting of each tail inclusion in each degree, not as complexes. -/
  degreewiseSplit : ∀ r n : ℤ, ∃ s : X.P.X n ⟶ (F.step r : CochainComplex _ ℤ).X n,
    (F.step r).arrow.f n ≫ s = 𝟙 _
  /-- The graded isomorphism is induced by the summand projection. -/
  gradedProjection : ∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
    (F.complexQuotientπ p.val (p.val + 1) (Int.le_add_one le_rfl)).f n ≫
        (gradedIso p).hom.f n =
      (F.step p.val).arrow.f n ≫ (X.coordinates n).hom ≫
        biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p
  /-- There are no other nonzero grades. -/
  outside : ∀ p : ℤ, (p < a ∨ b < p) → IsZero (F.gradedPiece p)

omit [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The tails are the direct sums of the summands of weight at least `r`.  Their
inclusions are chain maps because every matrix entry raises weight.  The finite
interval bounds and degreewise biproduct retractions give the splitting and
finiteness fields.  Taking the cokernel of two consecutive tails and cancelling
the next-tail summands gives the displayed graded isomorphism and projection;
outside the interval the two tails coincide.
(blueprint: lem-trf-finite-filtered-totalization-filtration) -/
theorem exists_finiteTwistingFiltrationData
    (a b : ℤ) (D : FiniteTwistingFamily R a b)
    (X : FiniteTwistingMatrixData D) :
    Nonempty (FiniteTwistingFiltrationData D X) :=
  ⟨{
    F := X.tailFiltration
    gradedIso := X.tailFiltrationGradedIso
    finite := ⟨a, b + 1, X.tailFiltration_step_eq_top le_rfl,
      X.tailFiltration_step_eq_bot (lt_add_one b)⟩
    bottomWeight := X.tailFiltration_step_eq_top le_rfl
    topWeight := X.tailFiltration_step_eq_bot (lt_add_one b)
    tailCoordinates := X.tailFiltrationCoordinates
    tailInclusion := X.tailFiltrationCoordinates_inv_arrow
    degreewiseSplit r n :=
      ⟨X.tailRetraction r n ≫ (X.tailFiltrationCoordinates r n).inv, by
        rw [X.tailFiltration_arrow_f, Category.assoc, X.tailι_tailRetraction_assoc,
          Iso.hom_inv_id]⟩
    gradedProjection p n := by
      rw [← HomologicalComplex.comp_f, X.complexQuotientπ_tailFiltrationGradedIso_hom,
        X.tailFiltration_arrow_f, Category.assoc,
        X.tailι_coordinates_hom_π p.val n ⟨p, le_rfl⟩]
      rfl
    outside := X.isZero_tailFiltration_gradedPiece }⟩

end CochainComplex
