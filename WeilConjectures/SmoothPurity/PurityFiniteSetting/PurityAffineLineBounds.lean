/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructure
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Open.OpenComplementCondition
public import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedAmbientAdjoint
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Finite
import WeilConjectures.AlgebraicGeometry.Etale.Closed.EtaleClosedSupportAmplitude
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityAffineLineGeometry
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityAffineLineTwistCover
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityAffineLineTwistTor
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructureStatement
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityBoundaryClosedTorTransport
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityConstantFiniteTor
import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Geometric and finiteness bounds for affine-line boundary realization

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, rank-one realization step.
(blueprint: lem-pur-affine-line-boundary-bounds).

This module assembles the geometric bound, the ordinary closed adjoint,
constructibility and Tor transport, and the common root-line trivializing cover.
The constant coefficient clause uses the proved constant_finiteTor theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

/-- The geometric and finiteness package for affine-line boundary realization.
Source: rank-one step of cor-pur-affine-space-zero-section-purity.proof.md.

Proof in words: finite type gives the affine-line dimension bound and the
finite-field open-complement theorem gives the punctured-line condition. The
ordinary closed adjoint and its amplitude theorems transport constructibility
and Tor finiteness. Finite etale twist trivializations give the two covers and
zero Tor interval; the Gysin structure supplies the remaining amplitude,
finite-Tor, and concentration clauses.
(blueprint: lem-pur-affine-line-boundary-bounds). -/
theorem affine_line_boundary_bounds (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    (∃ (d : ℕ) (hj : QuasiCompact (openImmersion Y)),
      topologicalKrullDim (Line Y) ≤ (d : WithBot ℕ∞) ∧
      @Scheme.HasOpenComplementCondition P.Coefficient inferInstance inferInstance
        (Punctured Y) (Line Y) (openImmersion Y) inferInstance hj (2 * d)) ∧
    ((Etale.lowerStar (Modules P) (zeroSection Y)).rightDerivedFunctor.IsLeftAdjoint) ∧
    (∀ M : DerivedCategory (EtSheaves P (Line Y)),
      Etale.DerivedCategory.isBoundedConstructible P.Coefficient (Line Y) M →
      Etale.DerivedCategory.isBoundedConstructible P.Coefficient Y
          ((etClosed P (zeroSection Y)).obj M) ∧
        (finiteTorConstructibleEtale P.coefficients.l P.extension P.level P.level_pos
            (Line Y) M →
          finiteTorConstructibleEtale P.coefficients.l P.extension P.level P.level_pos Y
            ((etClosed P (zeroSection Y)).obj M))) ∧
    (∃ V : Scheme.Cover.{u} Scheme.etalePrecoverage (Line Y), ∀ i : V.I₀,
      Nonempty ((Etale.upperStar (Modules P) (V.f i)).obj (P.twistEtale h (Line Y)) ≅
        P.constantEtale (V.X i)) ∧
      Nonempty ((upperStar (Modules P) (V.f i)).obj (P.twist h (Line Y)) ≅
        P.constant (V.X i))) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn P.Coefficient (Line Y) 0 0
      (P.gysinEtaleInput h Y).obj ∧
    Scheme.HasProEtaleTorAmplitude (Line Y) P.Ring
      ((finiteCoefficientIntrinsicRealization (Line Y) P.Ring).mapDerivedCategory.obj
        (P.gysinInput h Y).obj) 0 0 ∧
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((finiteCoefficientIntrinsicRealization Y P.Ring).mapDerivedCategory.obj
        (P.derivedSheaf h Y false)) ∧
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((finiteCoefficientIntrinsicRealization Y P.Ring).mapDerivedCategory.obj
        (P.gysinValue h Y)) ∧
    (∀ q : ℤ, q ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ProSheaves P Y) q).obj
        (P.gysinValue h Y))) := by
  obtain ⟨d, hj, hdim, hopen⟩ := affine_line_boundary_geometry P h Y a
  let := hj
  have hij : Set.range (zeroSection Y).base =
      (Set.range (openImmersion Y).base)ᶜ := by
    rw [show Set.range (openImmersion Y).base =
      (Set.range (zeroSection Y).base)ᶜ from AffineSpace.range_basicOpen_ι_coord Y]
    simp only [compl_compl]
  have hcd (M : EtSheaves P (Punctured Y)) (q : ℤ) (hq : (2 * d : ℕ) < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((Etale.lowerStar (Modules P) (openImmersion Y)).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) := by
    exact (hopen.1 M q hq).of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
      ((Etale.lowerStar (Modules P) (openImmersion Y)).rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj M)).symm)
  have hcons (M : EtSheaves P (Punctured Y)) (q : ℤ)
      (hM : Scheme.IsConstructibleEtaleModuleSheaf M) :
      Scheme.IsConstructibleEtaleModuleSheaf
        ((DerivedCategory.homologyFunctor _ q).obj
          ((Etale.lowerStar (Modules P) (openImmersion Y)).rightDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj M))) := by
    apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
    refine @Scheme.IsConstructibleSheaf.of_iso _ _ _ _ _ _ _ _ _ _ _
      ((DerivedCategory.homologyFunctor _ q).mapIso
        ((Etale.lowerStar (Modules P) (openImmersion Y)).rightDerivedFunctorPlusCompatibility.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj M))) ?_
    exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1
      (hopen.2 M q hM)
  have hpres (M : DerivedCategory (EtSheaves P (Line Y)))
      (hM : Etale.DerivedCategory.isBoundedConstructible P.Coefficient (Line Y) M) :
      Etale.DerivedCategory.isBoundedConstructible P.Coefficient Y
        ((etClosed P (zeroSection Y)).obj M) ∧
      (finiteTorConstructibleEtale P.coefficients.l P.extension P.level P.level_pos
        (Line Y) M →
        finiteTorConstructibleEtale P.coefficients.l P.extension P.level P.level_pos Y
          ((etClosed P (zeroSection Y)).obj M)) := by
    obtain ⟨a₀, b₀, hab, hv⟩ := hM.2
    have hc : (0 : ℤ) ≤ (2 * d : ℕ) := by positivity
    have hbounds : DerivedCategory.homologyConcentratedIn a₀ b₀ M :=
      ⟨(DerivedCategory.isGE_iff _ _).2 (fun q hq ↦ hv q (.inl hq)),
        (DerivedCategory.isLE_iff _ _).2 (fun q hq ↦ hv q (.inr hq))⟩
    obtain ⟨hQ, hQc⟩ := (Etale.closedImmersion_rightAdjoint_amplitude P.Coefficient
      (zeroSection Y) (openImmersion Y) hij a₀ b₀ ((2 * d : ℕ) : ℤ) hc hcd).2 hcons M hbounds hM.1
    have hbc : Etale.DerivedCategory.isBoundedConstructible P.Coefficient Y
        ((etClosed P (zeroSection Y)).obj M) := by
      refine ⟨hQc, a₀, b₀ + (2 * d : ℕ) + 1, by omega, fun q hq ↦ ?_⟩
      rcases hq with hq | hq
      · exact (DerivedCategory.isGE_iff _ _).1 hQ.1 q hq
      · exact (DerivedCategory.isLE_iff _ _).1 hQ.2 q hq
    refine ⟨hbc, ?_⟩
    rintro ⟨_, x, y, hxy, htor⟩
    have ht := (boundary_closed_tor_transport P (zeroSection Y) (openImmersion Y)
      hij x y ((2 * d : ℕ) : ℤ) hc hcd hcons M hM htor).2
    exact ⟨hbc, x, y + (2 * d : ℕ) + 1, by omega, ht⟩
  have ht := affine_line_boundary_twist_tor P h Y a
  have hg := P.gysin_structure_statement h Y a
  exact ⟨⟨d, hj, hdim, hopen⟩,
    Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion P.Coefficient
      (zeroSection Y), hpres, affine_line_boundary_cover P h Y a,
    ht.1, ht.2, constant_finiteTor P h Y, hg.1, hg.2.1⟩

end WeilConjectures.PurityFiniteSetting
