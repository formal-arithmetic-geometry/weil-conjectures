/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Paper.PuritySectionRestrictionData
public import Sheaf.Paper.DiagonalDncChartNormalization
public import Sheaf.Paper.FiniteRingSectionDeformation
public import Sheaf.Paper.FiniteSmoothCanonicalInterfaces

/-! # Integration on the actual normal-section invariant

The construction is reexported by SectionDncIntegrationSquare. Its value and
signature are unchanged; placing it before the naturality theorem allows the
normal-bundle square to be stated independently of DNC specialization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.SectionIntegration
open SectionRestriction

/-- Transport the inverse integration adjunct from the canonical conormal presentation
of the actual normal bundle, preserving its projection and augmentation.
Source: blueprint base-change factors (1), normal-bundle integration
(blueprint: def-pur-normal-section-integration-data). -/
def normalIntegration (P : PurityFiniteSetting.{u})
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (X : Pair B d) :
    Dnc.normalSection P d X.g aB X.s X.section_eq ≅ P.diagonalTwist B d := by
  letI := P.noetherian aB
  letI := SmoothOfRelativeDimension.smooth d X.g
  letI := Dnc.compactifiable P X.g aB
  letI := Etale.FiniteRingSectionDeformation.geometry d X.g X.s X.section_eq
  let F := ConormalGradedAlgebra.piece X.s 1
  let q := Etale.FiniteSmoothPurity.reesConeComparison X.s
  let c := Etale.FiniteRingSectionDeformation.coneBundleIso d X.g X.s
  let e := q ≪≫ c
  let π := Scheme.Hom.normalConeProj X.g X.s
  let πF := VectorBundleZeroSection.π B d F
  let z := X.s.normalConeZeroSection
  let zF := VectorBundleZeroSection.zero B d F
  letI := (Etale.vectorIntegration_geometry B d F).1
  letI := (Etale.vectorIntegration_geometry B d F).2.1
  letI := Dnc.compactifiable P πF aB
  letI := P.noetherian (πF ≫ aB)
  have hp : e.hom ≫ πF = π := by
    dsimp [e, πF, F]
    rw [Category.assoc,
      (Etale.FiniteRingSectionDeformation.coneBundleIso_spec d X.g X.s X.section_eq).1,
      (Etale.FiniteSmoothPurity.reesConeComparison_spec X.s).1,
      Scheme.Hom.purityNormalProjection_eq X.s X.g X.section_eq]
  have hz : z ≫ e.hom = zF := by
    dsimp [e, z, zF, F]
    rw [← Category.assoc, (Etale.FiniteSmoothPurity.reesConeComparison_spec X.s).2.1,
      (Etale.FiniteRingSectionDeformation.coneBundleIso_spec d X.g X.s X.section_eq).2]
  have wp : e.inv ≫ π = πF := by
    rw [← hp, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have wz : zF ≫ e.inv = z := by
    rw [← hz, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact Dnc.normalComparison P d X.g aB X.s X.section_eq ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
      (P.chartSectionEtaleRestriction N e.inv π πF wp z zF wz ≪≫
        Etale.FiniteRingSectionDeformation.bundleOrientation P.diagonalExponent
          (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
          P.diagonalExponent_annihilates B (P.diagonalExponent_isUnit aB) d F)

end WeilConjectures.PurityFiniteSetting.SectionIntegration
