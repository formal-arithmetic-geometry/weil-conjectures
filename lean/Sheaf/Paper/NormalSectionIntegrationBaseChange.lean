/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.NormalSectionIntegrationData
public import Sheaf.Paper.DiagonalOrientationRefinement
import Sheaf.Paper.VectorIntegrationSiteComparison
import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The base-change square for normal-bundle integration

Source: smooth-purity base-change factors (1), inverse vector-purity square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.SectionIntegration
open SectionRestriction

/-- The zero-section integration orientation on the actual normal bundle respects
arbitrary base change. This is the normal-bundle factor alone: neither DNC delta
nor the source section invariant enters the equation.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-purity-bc/sk-prop-sp-purity-bc-factors.proof.md, (1), vector integration;
lem-sp-section-dnc-integration-square, proof Steps 1, 3 and 4.
(blueprint: lem-pur-normal-section-integration-base-change).

Proof: the base-change map of extended Rees algebras fixes t and sends every
homogeneous ideal class to its pullback. At t=0 this identifies normalBaseChange
with pullback of the actual normal cone, preserving its projection and zero.
The homogeneous Rees comparison and relative Spec of the symmetric conormal
comparison intertwine this map with pullback of the conormal vector bundle.
Apply integration-normalized vector-bundle purity to that bundle at the
coefficient unit. If gamma is the integration adjunct, its equation is
exceptionalExchange * pull(gamma) = gamma' * TatePullback. Multiply by the
inverse adjuncts on the two sides and restrict along zero. Pullback composition
and the zero-section equation give exactly the ordinary-etale section square.
The normalized compact-support locality used in normalIntegration is the same
exceptional mate: both transpose inverse compact-support exchange followed by
the pulled-back counit. Mate pasting and the vector-integration site comparison
identify these maps with the pro-etale section exchange in baseComparison.
Naturality of the comparison-site pullback and of the normalized pure-root
Tate maps yields the displayed equation. No flatness is used. The rank-zero
bundle uses the empty ordered trace and identity shift; on the empty base
all the maps in the same square are the unique maps. -/
theorem normalIntegration_baseChange (P : PurityFiniteSetting.{u})
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    {B' B : Scheme.{u}} {d : ℕ}
    (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (aB' : B' ⟶ Spec (.of P.field.k)) [IsSeparated aB']
    [LocallyOfFiniteType aB'] [QuasiCompact aB']
    (b : B' ⟶ B) (_hb : b ≫ aB = aB')
    (X : Pair B d) (X' : Pair B' d) (sq : BaseChange b X' X) :
    baseComparison P aB aB' (normalBaseChange P aB aB' sq) ≪≫
        normalIntegration P N aB' X' =
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
          (normalIntegration P N aB X) ≪≫ OrientationRefinement.tate P b aB d := by sorry

end WeilConjectures.PurityFiniteSetting.SectionIntegration
