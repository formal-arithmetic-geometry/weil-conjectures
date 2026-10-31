/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateTowerNormalization.CoordinateTowerNormalizationData

import WeilConjectures.AlgebraicGeometry.CoordinateTowerNormalization.CoordinateTowerExceptionalCompositors
import WeilConjectures.AlgebraicGeometry.CoordinateTowerNormalization.CoordinateTowerNormalizationFusion
import WeilConjectures.AlgebraicGeometry.CoordinateTowerNormalization.CoordinateTowerCompactTranspose

/-! # Coordinate-tower normalization induction

Source: current blueprint, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, final paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.CoordinateTowerNormalization
open AffineZeroPurity AffineSpacePurity VectorIntegrationSite
attribute [local irreducible] rightDerivedUpperShriek rightDerivedLowerShriek
  originCompositionAmbient derivedComparisonAdjunction identityUnit

private theorem conjugate_unit_cancel {D : Type v} [Category.{w} D]
    {M N L : D} (t : M ⟶ N) (e : L ≅ N) (ht : IsIso t) :
    (t ≫ e.inv) ≫ 𝟙 L ≫ (e.hom ≫ @inv _ _ _ _ t ht) ≫ 𝟙 M = 𝟙 M := by
  have := ht
  simp only [Category.comp_id, Category.id_comp, Category.assoc,
    Iso.inv_hom_id_assoc, IsIso.hom_inv_id]

private def zeroIdentityIso
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] :=
  letI : IsNoetherian B := tower_noetherian (setting P n) B aB 0
  letI hId : HasCompactification (𝟙 B) := HasCompactification.of_isProper (𝟙 B)
  letI hZero : HasCompactification (zero B 0 : B ⟶ B) :=
    @HasCompactification.of_eq B B (𝟙 B) (zero B 0) hId (zero_zero B).symm
  (@rightDerivedUpperShriekCongr
    (setting P n).Coefficient inferInstance inferInstance
    B B (zero B 0) (𝟙 B) (zero_zero B) hZero hId).app (unit P n B)

private theorem lineLaw_mono
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    {c d : ℕ} (h : d ≤ c) (hl : LineLaw P n B aB c) : LineLaw P n B aB d := by
  unfold LineLaw at hl ⊢
  intro r
  exact hl ⟨r.val, Nat.lt_of_lt_of_le r.isLt h⟩

private theorem thetaStep_eq
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (c : ℕ) (u : Orientations P n B c) (r : ℕ) (hr : r < c)
    (previous : ThetaHom P n B r) :
    thetaStep P n B aB c u r hr previous = previous ≫
      (rightDerivedUpperShriek (setting P n).Coefficient
        (zero B r)).map (u ⟨r, hr⟩) ≫ closedCompositionInverse P n B aB r := by
  unfold thetaStep thetaStepRaw mapComposition
  simp

private theorem theta_succ
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (c : ℕ) (u : Orientations P n B c) (r : ℕ) (hr : r + 1 ≤ c) :
    theta P n B aB c u (r + 1) hr =
      thetaStep P n B aB c u r (Nat.lt_of_succ_le hr)
        (theta P n B aB c u r (Nat.le_of_succ_le hr)) := by
  unfold theta
  rw [orderedRec]

private theorem theta_zero_normalized
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (c : ℕ) (u : Orientations P n B c) :
    theta P n B aB c u 0 (Nat.zero_le c) ≫ normalization P n B aB 0 =
      𝟙 (coefficientUnit P n B) := by
  have : IsNoetherian B := tower_noetherian (setting P n) B aB 0
  unfold coefficientUnit at *
  unfold theta orderedRec thetaZero normalization normalizationRaw coefficientUnit
  erw [eqToHom_refl, eqToHom_refl]
  · dsimp only
    exact conjugate_unit_cancel
      (identityUnit (setting P n).Coefficient B (unit P n B) (unit_origin P n B))
      (zeroIdentityIso P n B aB) (identityUnit_isIso _ _ _ (unit_origin P n B))
  all_goals rfl

private theorem gamma_isIso
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (c : ℕ) (hl : LineLaw P n B aB c) (r : ℕ) (hr : r ≤ c) :
    IsIso (gamma P n B aB r) := by
  induction r with
  | zero =>
    unfold gamma affineSpacePurityComparison orderedRec comparisonZero
    delta orderedSource exceptional
    dsimp only [id]
    exact @CategoryTheory.IsIso.id
      (AffineSpacePurity.D (setting P n) (iteratedAffineLine B 0)) inferInstance _
  | succ r ih =>
    have hprev := ih (Nat.le_of_succ_le hr)
    have hcomp := (exceptionalCompositors_isIso P n B aB r).1
    let K : Plus (setting P n).Coefficient B := ⟨_, (unit_origin P n B).plus⟩
    let Ke := (_root_.DerivedCategory.singleFunctor _ 0).obj ((setting P n).constantEtale B)
    let hKe := unit_finiteTor P n B
    let eK := (Functor.mapDerivedCategorySingleFunctor
      (comparisonUpperStar (ModuleCat.{u + 1} (setting P n).Coefficient) B) 0).app
        ((setting P n).constantEtale B) ≪≫ (eqToIso (unit_single_eq P n B)).symm
    have hstage := stage_applicability (setting P n) B aB K Ke hKe eK r
    unfold LineLaw at hl
    have hline := hl ⟨r, Nat.lt_of_succ_le hr⟩
    have hi := hline.1
      ⟨(exceptional (setting P n) B r).obj K.obj, hstage.1⟩
      (stageEtale (setting P n) B K.obj Ke r)
      hstage.2
      (stageComparison (setting P n) B K.obj Ke eK r)
    unfold lineGamma at hi
    unfold gamma affineSpacePurityComparison
    rw [orderedRec]
    dsimp only [comparisonStep]
    unfold gamma affineSpacePurityComparison at hprev
    let hprevIso : IsIso (orderedRec (comparisonZero (setting P n) B (unit P n B))
        (comparisonStep (setting P n) B aB K Ke hKe eK) r) := hprev
    have hm : IsIso ((lineSource (setting P n) (iteratedAffineLine B r)).map
        (orderedRec (comparisonZero (setting P n) B (unit P n B))
          (comparisonStep (setting P n) B aB K Ke hKe eK) r)) := by
      infer_instance
    exact CategoryTheory.IsIso.comp_isIso'
      (sourceReassociation (setting P n) B aB (unit P n B) r).isIso_hom
      (CategoryTheory.IsIso.comp_isIso' hm
        (CategoryTheory.IsIso.comp_isIso' hi hcomp))

/-- Ordered normalization induction, with the actual cancellation and transpose identities.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, final paragraph
(blueprint: lem-pur-coordinate-tower-normalization-induction).
Proof:
1. Finite Tate lines are etale locally free of rank one with finite stalks by
lem-pur-twist-sheaf-locally-free (3). Their r-fold tensor power, shifted by 2r,
is constructible with Tor amplitude [-2r,-2r]; r=0 is the coefficient unit.
lem-sf-proetale-constructible-origin supplies the bounded-below origin domain.
2. Induct from gamma_0=id using the recorded four-arrow recursion. Naturality
of the line comparison rewrites its successor as c_r^-1 Q_r(gamma_r) v_r.
The three factors are invertible. This also supplies W_r as the finite-Tor
witness for every target; no purity theorem for arbitrary smooth maps is used.
3. Apply associativity and identity normalization of thm-sf-comp-composition
to z_r,s_r,q_r,p_r. Conjugate that equation by
 def-weil-pbc-adjunction-conjugate, with the pasted adjunction of
 def-weil-pbc-composite-adjunction and lem-weil-pbc-mate-pasting (2),(4).
The result is the equality of the two contractions of Z_r S_r Q_r P_r.
4. At zero, gamma and theta are identities. The exceptional contraction is
the conjugate of the identity compact-support compositor, hence is identity.
5. Expand b_(r+1) theta_(r+1). Move d_r^-1 past the next map by naturality,
apply the contraction equation of Step 3, and move gamma_r past e_(q_r).
The assumed u_r evaluation then cancels the last factor. The remaining
composite is b_r theta_r. Induction gives b_c theta_c=1.
6. If all u_r are invertible, the recurrence makes all theta_r invertible.
Right-multiplication of b_r theta_r=1 by theta_r^-1 gives b_r=theta_r^-1.
7. Properness of z_r identifies Rz_! with z_*. Its complement is quasi-compact:
over each member of a finite affine cover of B it is the finite union of D(t_i).
The identity-normalized compact-support compositor gives sourceIdentification,
as in lem-pur-closed-section-compact-origin. Define C_r by the closed adjunction.
8. Write a_r and C_r with the two exceptional counits. Naturality of the
closed counit, followed by the composite counit formula and its conjugate,
identifies their composite under sourceIdentification with b_r theta_r=1.
For c=0 every displayed comparison is its canonical identity normalization;
for empty B every object and map is zero. -/
theorem coordinateTower_normalization_induction
    (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    (c : ℕ) (hline : LineLaw P n B aB c) (u : Orientations P n B c)
    (hu : ∀ r : Fin c,
      u r ≫
        (rightDerivedUpperShriek (setting P n).Coefficient
          (lastSection B r.val)).map (targetLineGamma P n B aB r.val) ≫
        lineCollapse P n B aB r.val = 𝟙 (tatePower P n (iteratedAffineLine B r.val) r.val)) :
    (∀ (r : ℕ) (_hr : r ≤ c), IsIso (gamma P n B aB r) ∧
      ∃ e : tatePower P n (iteratedAffineLine B r) r ≅
        (exceptional (setting P n) B r).obj (coefficientUnit P n B),
        e.hom = (targetSourceIso P n B r).hom ≫ gamma P n B aB r ∧
        DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (setting P n).Coefficient) (iteratedAffineLine B r)
          (tatePower P n (iteratedAffineLine B r) r)) ∧
    theta P n B aB c u 0 (Nat.zero_le c) ≫ normalization P n B aB 0 = 𝟙 (coefficientUnit P n B) ∧
    (∀ r : Fin c,
      theta P n B aB c u (r.val + 1) (Nat.succ_le_of_lt r.isLt) ≫
          normalization P n B aB (r.val + 1) =
        theta P n B aB c u r.val (Nat.le_of_lt r.isLt) ≫ normalization P n B aB r.val) ∧
    theta P n B aB c u c le_rfl ≫ normalization P n B aB c = 𝟙 (coefficientUnit P n B) ∧
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
      (iteratedAffineLineProj B c)).map (classMap P n B aB c u c le_rfl) ≫
        augmentation P n B aB c = (sourceIdentification P n B aB c).hom ∧
    ((∀ r : Fin c, IsIso (u r)) → ∀ (r : ℕ) (hr : r ≤ c),
      ∃ ht : IsIso (theta P n B aB c u r hr),
        normalization P n B aB r = @inv _ _ _ _ (theta P n B aB c u r hr) ht) := by
  have : IsNoetherian B := tower_noetherian (setting P n) B aB 0
  have hzero := theta_zero_normalized P n B aB c u
  have hstep : ∀ r : Fin c,
      theta P n B aB c u (r.val + 1) (Nat.succ_le_of_lt r.isLt) ≫
          normalization P n B aB (r.val + 1) =
        theta P n B aB c u r.val (Nat.le_of_lt r.isLt) ≫
          normalization P n B aB r.val := by
    intro r
    rw [theta_succ, thetaStep_eq]
    simp only [Category.assoc]
    rw [normalization_fusion P n B aB r.val
      (lineLaw_mono P n B aB (Nat.succ_le_of_lt r.isLt) hline)]
    rw [← Functor.map_comp_assoc, hu r, CategoryTheory.Functor.map_id, Category.id_comp]
  have hall : ∀ (r : ℕ) (hr : r ≤ c),
      theta P n B aB c u r hr ≫ normalization P n B aB r =
        𝟙 (coefficientUnit P n B) := by
    intro r
    induction r with
    | zero => intro hr; exact hzero
    | succ r ih =>
      intro hr
      exact (hstep ⟨r, Nat.lt_of_succ_le hr⟩).trans (ih (Nat.le_of_succ_le hr))
  refine ⟨?_, hzero, hstep, hall c le_rfl, ?_, ?_⟩
  · intro r hr
    have hi := gamma_isIso P n B aB c hline r hr
    exact ⟨hi, ⟨targetSourceIso P n B r ≪≫ @asIso _ _ _ _ (gamma P n B aB r) hi,
      rfl, (target_properties P n B aB r).1⟩⟩
  · unfold classMap
    rw [compact_transpose P n B aB c, hall c le_rfl, Category.comp_id]
  · intro huIso r hr
    have ht : IsIso (theta P n B aB c u r hr) := by
      induction r with
      | zero =>
        unfold theta orderedRec thetaZero
        have hi := identityUnit_isIso (setting P n).Coefficient B
          (coefficientUnit P n B) (unit_origin P n B)
        apply CategoryTheory.IsIso.comp_isIso' hi
        exact (zeroIdentityIso P n B aB).isIso_inv
      | succ r ih =>
        have hp := ih (Nat.le_of_succ_le hr)
        have hs := huIso ⟨r, Nat.lt_of_succ_le hr⟩
        have hd := (exceptionalCompositors_isIso P n B aB r).2
        rw [theta_succ, thetaStep_eq]
        infer_instance
    refine ⟨ht, ?_⟩
    apply (cancel_epi (theta P n B aB c u r hr)).1
    rw [hall r hr, IsIso.hom_inv_id]

end AlgebraicGeometry.ProEtale.CoordinateTowerNormalization
