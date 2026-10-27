/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Paper.NormalSectionIntegrationData
public import Sheaf.Paper.PuritySectionEtaleRestriction
public import Sheaf.Paper.DiagonalDncChartNormalization
public import Sheaf.Paper.FiniteRingSectionDeformation
public import Sheaf.Paper.FiniteSmoothCanonicalInterfaces
public import Sheaf.Paper.DiagonalOrientationRefinement
public import Sheaf.Paper.DiagonalOrientationCharts
public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.Paper.PuritySectionInvariantIntrinsic
public import Sheaf.Paper.PurityDncFamilyIntrinsic
public import Sheaf.Paper.PurityNormalProjection
public import Sheaf.Paper.PurityDncInvariance
public import Sheaf.Paper.VectorBundlePurity
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.PurityDiagonalDualizingObject
public import Sheaf.Paper.PurityDncComparisons
public import Sheaf.Paper.PurityDiagonalBaseChangeCompared
public import Sheaf.Paper.PurityFiniteSetting
import Sheaf.Paper.NormalSectionIntegrationBaseChange
import Sheaf.Paper.NormalSectionIntegrationOrientation
import Sheaf.Paper.DiagonalDncAssemblyGlobal

/-! # Base change of the integrated deformation comparison

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-purity-bc/
sk-prop-sp-purity-bc-factors.proof.md, (1)
(blueprint: lem-sp-section-dnc-integration-square).

The zero fibre is the actual associated-graded normal cone. Its homogeneous Rees
comparison identifies it with the relative spectrum of the symmetric conormal algebra.
The normal orientation is the inverse of the actual integration adjunct, restricted
along zero; no trivial bundle or independent orientation is supplied.
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

/-- The integrated DNC comparison psi = z* b_N composed with delta. Delta is the
uniquely coordinate-normalized comparison, and the normal bundle carries exactly
its integration-adjunction orientation.
Source: blueprint base-change factors (1), displayed composite
(blueprint: lem-sp-section-dnc-integration-square). -/
def psi (P : PurityFiniteSetting.{u})
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    {B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB] (X : Pair B d) :
    invariant P aB X ≅ P.diagonalTwist B d :=
  delta P aB X ≪≫ normalIntegration P N aB X

/-- Arbitrary base change preserves the integrated DNC comparison. The bottom
coefficient extension specializes the finite purity convention to Z/ell^r, r >= 1.
The normalized compact-support presentation N ranges over presentations of the
same counit-defined operations; it is not an orientation or exchange chosen by hand.
The Cartesian square includes the pulled-back section. No flatness, positive rank,
nonemptiness, or additional constructibility hypothesis is imposed.
Source: blueprint base-change factors (1)
(blueprint: lem-sp-section-dnc-integration-square).

Proof: the normalized-base component of SectionRestriction.coherence gives
baseComparison followed by delta' = pullback(delta) followed by the normal
baseComparison. normalIntegration_baseChange gives the square for the normal
factor, including the actual integration adjunct and its counit-defined exchange.
Unfold psi, reassociate, substitute these two equations, and use functoriality
of pullback on composition. No flatness or positive-rank assumption is used;
the two component equations include empty schemes and rank zero. -/
theorem section_dnc_integration_baseChange (P : PurityFiniteSetting.{u})
    (_hE : P.extension = ⊥)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    {B' B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB' : B' ⟶ Spec (.of P.field.k)) [IsSeparated aB']
    [LocallyOfFiniteType aB'] [QuasiCompact aB']
    (b : B' ⟶ B) (_hb : b ≫ aB = aB')
    (X : Pair B d) (X' : Pair B' d) (sq : BaseChange b X' X) :
    baseComparison P aB aB' sq ≪≫ psi P N aB' X' =
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
          (psi P N aB X) ≪≫ OrientationRefinement.tate P b aB d := by
  have hδ := ((coherence P).2.2.2.1 B B' aB aB' b _hb d X X' sq).2.2
  have hβ := normalIntegration_baseChange P N aB aB' b _hb X X' sq
  dsimp only [psi]
  calc
    _ = (baseComparison P aB aB' sq ≪≫ delta P aB' X') ≪≫
        normalIntegration P N aB' X' := by rw [Iso.trans_assoc]
    _ = ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (delta P aB X) ≪≫
        baseComparison P aB aB' (normalBaseChange P aB aB' sq)) ≪≫
        normalIntegration P N aB' X' := by rw [hδ]
    _ = _ := by rw [Iso.trans_assoc, hβ, ← Iso.trans_assoc, ← Functor.mapIso_trans]

/-- The diagonal specialization is the normalized diagonal orientation.
Source: blueprint base-change factors (1), final diagonal identification
(blueprint: lem-sp-section-dnc-integration-square). -/
def diagonalPair {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f] : Pair X d where
  V := pullback f f
  g := pullback.fst f f
  s := pullback.diagonal f
  smooth := inferInstance
  separated := inferInstance
  quasiCompact := inferInstance
  closed := inferInstance
  section_eq := pullback.diagonal_fst f

/-- The diagonal assembly is psi composed with kappa inverse; kappa is the
inverse exceptional base-change mate restricted to the actual diagonal. This
identifies the composite with the orientation whose chart normalization is
specified in det-sp-orientation-charts.
Source: blueprint base-change factors (1), diagonal clause
(blueprint: lem-sp-section-dnc-integration-square).

Proof: use the canonical normalized Tate transport. By
normalIntegration_eq_sectionOrientation the normal factor is chartDiagonalBeta.
The normalization proofs of the two DNC maps give their equality by uniqueness.
The existing diagonalDncAssemblyGlobal identifies the orientation with the
specified alpha inverse, delta and beta. Substitution and associativity prove
the formula, including rank zero and empty schemes. -/
theorem section_dnc_integration_diagonal (P : PurityFiniteSetting.{u})
    (_hE : P.extension = ⊥)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [IsSeparated aY]
    [LocallyOfFiniteType aY] [QuasiCompact aY] :
    (P.chartDiagonalAlpha d f aY).symm ≪≫ psi P N (f ≫ aY) (diagonalPair d f) =
      P.diagonalDualizingObject d f aY := by
  let t := purityTwistTransport P.Coefficient P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates
  rw [P.diagonalDncAssemblyGlobal d f aY t]
  dsimp only [psi]
  rw [normalIntegration_eq_sectionOrientation P N (f ≫ aY) (diagonalPair d f) t]
  have hδ : delta P (f ≫ aY) (diagonalPair d f) = P.chartDiagonalDelta d f aY := by
    let h := Dnc.existsUnique_dncInvariance P d (pullback.fst f f) (f ≫ aY)
      (pullback.diagonal f) (pullback.diagonal_fst f)
    exact h.unique (Classical.choose_spec h).1 h.exists.choose_spec
  rw [hδ]
  dsimp only [chartDiagonalAssembly, chartDiagonalBeta, diagonalPair]


end WeilConjectures.PurityFiniteSetting.SectionIntegration
