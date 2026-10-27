/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.NormalSectionIntegrationData
import Sheaf.Paper.NormalModelSectionOrientation
import Sheaf.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness

/-! # Agreement of the two normal-section orientation presentations

Source: smooth-purity chart proof Step 4, normal-bundle integration normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.SectionIntegration
open SectionRestriction

/-- The conormal-model integration orientation is the zero-section restriction
of the normalized orientation of the actual normal projection. This identifies
only the normal factor; it does not involve DNC specialization or diagonal assembly.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-orientation/sk-prop-sp-orientation-charts.proof.md, Step 4;
sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md, (1).
(blueprint: lem-pur-normal-section-integration-orientation).

Proof: use the homogeneous Rees comparison followed by relative Spec of the
symmetric conormal comparison. This is the bundle model in normalIntegration;
its inverse preserves the projection and augmentation by reesConeComparison_spec
and coneBundleIso_spec. Apply normalModelSectionOrientation to this inverse,
the actual normal projection and its zero section. For gamma take the actual
bundle integration adjunct, precomposed with inverse canonical Tate pullback
along the bundle projection. Its invertibility is bundleAdjoint_isIso.
The defining hom equation of gamma is precisely the integration adjunction.
In the resulting section formula, pullback of inverse gamma followed by Tate
restriction equals inverse bundleSectionAdjoint: Tate pullback composition
identifies its two coefficient constraints with the section compositor for
pi z = identity. The comparison from the tensor unit to the degree-zero
coefficient object is chartDualizingUnit on both sides. Functoriality and the
inverse equations cancel these unit comparisons. Thus the formula is the
etale locality factor followed by bundleOrientation, exactly the ordinary
part of normalIntegration. Apply the comparison-site functor and precompose
with normalComparison. The pure-root normalization fixes the same Tate map
for every normalized transport t. The empty tensor and identity compositor
prove rank zero; the same equations on the empty site are unique. -/
theorem normalIntegration_eq_sectionOrientation (P : PurityFiniteSetting.{u})
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB] (X : Pair B d)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := P.noetherian aB
    letI : SmoothOfRelativeDimension d (Scheme.Hom.normalConeProj X.g X.s) :=
      (normalPair P aB X).smooth
    letI := SmoothOfRelativeDimension.smooth d (Scheme.Hom.normalConeProj X.g X.s)
    letI : IsSeparated (Scheme.Hom.normalConeProj X.g X.s) :=
      (normalPair P aB X).separated
    letI := Dnc.normalQuasiCompact d X.g X.s X.section_eq
    normalIntegration P N aB X =
      Dnc.normalComparison P d X.g aB X.s X.section_eq ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
          (P.chartSectionOrientation d (Scheme.Hom.normalConeProj X.g X.s) aB
            X.s.normalConeZeroSection t) := by sorry

end WeilConjectures.PurityFiniteSetting.SectionIntegration
