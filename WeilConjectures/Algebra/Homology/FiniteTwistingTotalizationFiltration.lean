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
/-- If two subobjects coincide, the cokernel of the inclusion between them vanishes. -/
lemma CategoryTheory.Subobject.isZero_cokernel_ofLE_of_eq {𝒞 : Type*} [Category 𝒞]
    [Abelian 𝒞] {A : 𝒞} {S T : Subobject A} (h : S ≤ T) (e : S = T) :
    IsZero (cokernel (Subobject.ofLE S T h)) := by
  subst e
  have : IsIso (Subobject.ofLE S S h) := by
    rw [Subobject.ofLE_refl]
    infer_instance
  exact isZero_cokernel_of_epi _

namespace CochainComplex
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})
variable {R} {a b : ℤ}

/-- The filtration data required to turn matrix data into a realization record. -/
structure FiniteTwistingFiltrationData
    (D : FiniteTwistingFamily R a b) (X : FiniteTwistingMatrixData D) where
  F : DecreasingFiltration X.P
  gradedIso : ∀ p : ↥(Finset.Icc a b), F.gradedPiece p.val ≅ D.G p
  finite : F.IsFinite
  bottomWeight : F.step a = ⊤
  topWeight : F.step (b + 1) = ⊥
  tailCoordinates : ∀ r n : ℤ,
    ((F.step r : CochainComplex _ ℤ).X n) ≅
      ⨁ fun p : {p : ↥(Finset.Icc a b) // r ≤ p.val} ↦ (D.G p.val).X n
  tailInclusion : ∀ r n : ℤ,
    (tailCoordinates r n).inv ≫ (F.step r).arrow.f n =
      biproduct.desc (fun p : {p : ↥(Finset.Icc a b) // r ≤ p.val} ↦
        biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p.val ≫
          (X.coordinates n).inv)
  degreewiseSplit : ∀ r n : ℤ, ∃ s : X.P.X n ⟶ (F.step r : CochainComplex _ ℤ).X n,
    (F.step r).arrow.f n ≫ s = 𝟙 _
  gradedProjection : ∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
    (F.complexQuotientπ p.val (p.val + 1) (Int.le_add_one le_rfl)).f n ≫
        (gradedIso p).hom.f n =
      (F.step p.val).arrow.f n ≫ (X.coordinates n).hom ≫
        biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p
  outside : ∀ p : ℤ, (p < a ∨ b < p) → IsZero (F.gradedPiece p)

namespace FiniteTwistingMatrixData

variable {D : FiniteTwistingFamily R a b} (X : FiniteTwistingMatrixData D)

omit [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The arrow of a step of the tail filtration is the tail inclusion. -/
lemma tailFiltration_arrow (r : ℤ) :
    (X.tailFiltration.F r).arrow = (Subobject.underlyingIso (X.tailι r)).hom ≫ X.tailι r :=
  (Subobject.underlyingIso_hom_comp_eq_mk _).symm

omit [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The inclusion of two steps of the tail filtration is the inclusion of tails. -/
lemma ofLE_tailFiltration {r r' : ℤ} (h : r ≤ r')
    (hle : X.tailFiltration.F r' ≤ X.tailFiltration.F r) :
    Subobject.ofLE (X.tailFiltration.F r') (X.tailFiltration.F r) hle =
      (Subobject.underlyingIso (X.tailι r')).hom ≫ X.tailMap h ≫
        (Subobject.underlyingIso (X.tailι r)).inv := by
  rw [← cancel_mono (X.tailFiltration.F r).arrow, Subobject.ofLE_arrow, tailFiltration_arrow,
    tailFiltration_arrow, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    tailMap_comp_tailι]

omit [HasWeakSheafify J AddCommGrpCat.{w}] in
@[reassoc]
lemma tailMap_comp_underlyingIso_inv {r r' : ℤ} (h : r ≤ r')
    (hle : X.tailFiltration.F r' ≤ X.tailFiltration.F r) :
    X.tailMap h ≫ (Subobject.underlyingIso (X.tailι r)).inv =
      (Subobject.underlyingIso (X.tailι r')).inv ≫
        Subobject.ofLE (X.tailFiltration.F r') (X.tailFiltration.F r) hle := by
  rw [X.ofLE_tailFiltration h, Iso.inv_hom_id_assoc]

omit [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The tails of weight at most `a` are everything. -/
lemma tailFiltration_F_eq_top {r : ℤ} (h : r ≤ a) : X.tailFiltration.F r = ⊤ := by
  have (n : ℤ) : IsIso ((X.tailι r).f n) := by
    rw [tailι_f]
    have : IsIso (D.tailIncl r n) :=
      ⟨D.tailProj r n, D.tailIncl_tailProj r n, D.tailProj_tailIncl_of_le h n⟩
    infer_instance
  have := HomologicalComplex.Hom.isIso_of_components (X.tailι r)
  exact Subobject.mk_eq_top_of_isIso _

omit [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The tails of weight greater than `b` are zero. -/
lemma tailFiltration_F_eq_bot {r : ℤ} (h : b < r) : X.tailFiltration.F r = ⊥ := by
  rw [tailFiltration_F, Subobject.mk_eq_bot_iff_zero]
  ext n
  rw [tailι_f, D.tailIncl_eq_zero h, zero_comp, HomologicalComplex.zero_f]

/-- The projection of the graded piece of weight `p` of the tail filtration onto `D.G p`. -/
noncomputable def tailGradedPieceHom (p : ↥(Finset.Icc a b)) :
    X.tailFiltration.gradedPiece p.val ⟶ D.G p :=
  cokernel.desc (Subobject.ofLE (X.tailFiltration.F (p.val + 1)) (X.tailFiltration.F p.val)
      (X.tailFiltration.F_succ_le p.val))
    ((Subobject.underlyingIso (X.tailι p.val)).hom ≫ X.tailGradedπ p) (by
    rw [X.ofLE_tailFiltration (Int.le_add_one le_rfl)]
    simp)

@[reassoc]
lemma π_tailGradedPieceHom (p : ↥(Finset.Icc a b))
    (hle : X.tailFiltration.F (p.val + 1) ≤ X.tailFiltration.F p.val) :
    cokernel.π (Subobject.ofLE (X.tailFiltration.F (p.val + 1)) (X.tailFiltration.F p.val) hle) ≫
        X.tailGradedPieceHom p =
      (Subobject.underlyingIso (X.tailι p.val)).hom ≫ X.tailGradedπ p :=
  cokernel.π_desc _ _ _

/-- The inverse of `tailGradedPieceHom`, induced by the cokernel property of `D.G p`. -/
noncomputable def tailGradedPieceInv (p : ↥(Finset.Icc a b)) :
    D.G p ⟶ X.tailFiltration.gradedPiece p.val :=
  (X.tailShortComplex_shortExact p).gIsCokernel.desc (CokernelCofork.ofπ
    ((Subobject.underlyingIso (X.tailι p.val)).inv ≫
      cokernel.π (Subobject.ofLE (X.tailFiltration.F (p.val + 1)) (X.tailFiltration.F p.val)
        (X.tailFiltration.F_succ_le p.val))) (by
        rw [tailShortComplex_f, X.tailMap_comp_underlyingIso_inv_assoc _
          (X.tailFiltration.F_succ_le p.val), cokernel.condition, comp_zero]))

@[reassoc]
lemma tailGradedπ_comp_tailGradedPieceInv (p : ↥(Finset.Icc a b)) :
    X.tailGradedπ p ≫ X.tailGradedPieceInv p =
      (Subobject.underlyingIso (X.tailι p.val)).inv ≫
        cokernel.π (Subobject.ofLE (X.tailFiltration.F (p.val + 1)) (X.tailFiltration.F p.val)
          (X.tailFiltration.F_succ_le p.val)) :=
  Cofork.IsColimit.π_desc (X.tailShortComplex_shortExact p).gIsCokernel

/-- The graded piece of weight `p` of the tail filtration is `D.G p`. -/
noncomputable def tailGradedIso (p : ↥(Finset.Icc a b)) :
    X.tailFiltration.gradedPiece p.val ≅ D.G p where
  hom := X.tailGradedPieceHom p
  inv := X.tailGradedPieceInv p
  hom_inv_id := coequalizer.hom_ext (by
    rw [X.π_tailGradedPieceHom_assoc, tailGradedπ_comp_tailGradedPieceInv,
      Iso.hom_inv_id_assoc]
    exact (Category.comp_id _).symm)
  inv_hom_id := by
    have : Epi (X.tailGradedπ p) := (X.tailShortComplex_shortExact p).epi_g
    rw [← cancel_epi (X.tailGradedπ p), tailGradedπ_comp_tailGradedPieceInv_assoc,
      π_tailGradedPieceHom, Iso.inv_hom_id_assoc, Category.comp_id]

lemma tailGradedIso_hom (p : ↥(Finset.Icc a b)) :
    (X.tailGradedIso p).hom = X.tailGradedPieceHom p :=
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The inverse coordinate isomorphism followed by the arrow of a step is the tail
inclusion. -/
@[reassoc]
lemma underlyingIso_inv_comp_tailFiltration_arrow (r : ℤ) :
    (Subobject.underlyingIso (X.tailι r)).inv ≫ (X.tailFiltration.F r).arrow = X.tailι r := by
  rw [tailFiltration_arrow, Iso.inv_hom_id_assoc]

omit [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Outside the weight interval the graded pieces of the tail filtration vanish. -/
lemma isZero_tailFiltration_gradedPiece {p : ℤ} (hp : p < a ∨ b < p) :
    IsZero (X.tailFiltration.gradedPiece p) := by
  refine Subobject.isZero_cokernel_ofLE_of_eq _ ?_
  rcases hp with hp | hp
  · rw [X.tailFiltration_F_eq_top (by omega), X.tailFiltration_F_eq_top hp.le]
  · rw [X.tailFiltration_F_eq_bot (by omega), X.tailFiltration_F_eq_bot hp]

end FiniteTwistingMatrixData

/-- The tails are the direct sums of the summands of weight at least `r`.  Their
inclusions are chain maps because every matrix entry raises weight.  The finite
interval bounds and degreewise biproduct retractions give the splitting and
finiteness fields.  Taking the cokernel of two consecutive tails and cancelling
the next-tail summands gives the displayed graded isomorphism and projection;
outside the interval the two tails coincide.
(blueprint: lem-trf-finite-filtered-totalization-filtration) -/
theorem exists_finiteTwistingFiltrationData
    (a b : ℤ) (hab : a ≤ b) (D : FiniteTwistingFamily R a b)
    (X : FiniteTwistingMatrixData D) :
    ∃ F : FiniteTwistingFiltrationData D X, True := by
  refine ⟨{ F := X.tailFiltration
            gradedIso := X.tailGradedIso
            finite := ⟨a, b + 1, X.tailFiltration_F_eq_top le_rfl,
              X.tailFiltration_F_eq_bot (by omega)⟩
            bottomWeight := X.tailFiltration_F_eq_top le_rfl
            topWeight := X.tailFiltration_F_eq_bot (by omega)
            tailCoordinates := fun r n ↦
              (HomologicalComplex.eval _ _ n).mapIso (Subobject.underlyingIso (X.tailι r))
            tailInclusion := fun r n ↦ ?_
            degreewiseSplit := fun r n ↦ ⟨(X.coordinates n).hom ≫ D.tailProj r n ≫
              (Subobject.underlyingIso (X.tailι r)).inv.f n, ?_⟩
            gradedProjection := fun p n ↦ ?_
            outside := fun _ hp ↦ X.isZero_tailFiltration_gradedPiece hp }, trivial⟩
  · rw [Functor.mapIso_inv, HomologicalComplex.eval_map,
      ← HomologicalComplex.comp_f, X.underlyingIso_inv_comp_tailFiltration_arrow,
      FiniteTwistingMatrixData.tailι_f]
    refine biproduct.hom_ext' _ _ fun q ↦ ?_
    rw [FiniteTwistingFamily.ι_tailIncl_assoc, biproduct.ι_desc]
  · rw [FiniteTwistingMatrixData.tailFiltration_arrow,
      HomologicalComplex.comp_f, Category.assoc,
      FiniteTwistingMatrixData.tailι_f_retraction_assoc]
    exact (whisker_eq _ (Category.id_comp _)).trans
      ((HomologicalComplex.eval _ _ n).mapIso (Subobject.underlyingIso (X.tailι r))).hom_inv_id
  · rw [DecreasingFiltration.complexQuotientπ, ← HomologicalComplex.comp_f,
      FiniteTwistingMatrixData.tailGradedIso_hom,
      FiniteTwistingMatrixData.π_tailGradedPieceHom,
      FiniteTwistingMatrixData.tailFiltration_arrow, HomologicalComplex.comp_f,
      HomologicalComplex.comp_f, Category.assoc, FiniteTwistingMatrixData.tailι_f,
      FiniteTwistingMatrixData.tailGradedπ_f, Category.assoc, Iso.inv_hom_id_assoc,
      FiniteTwistingFamily.tailIncl_π_of_le _ _ _ _ le_rfl]

end CochainComplex
