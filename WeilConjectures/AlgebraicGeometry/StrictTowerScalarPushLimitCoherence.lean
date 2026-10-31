/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTowerRealizationComparisons

/-! # Scalar compatibility of the specified direct-image/strict-limit comparisons.
Source: Stacks 0A07 and the flat scalar direct-image/limit coherence theorem.
(blueprint: lem-cbc-strict-tower-scalar-push-limit-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The completed and constant direct-image/limit comparisons form the normalized
scalar square on every derived strict tower, without a completeness assumption.

Source: Stacks Project, sites-cohomology.tex, lemma-Rf-commutes-with-Rlim (0A07);
flatScalarDirectImageLimitCoherence; strict realization proof Step 8.
(blueprint: lem-cbc-strict-tower-scalar-push-limit-coherence).
Proof: apply flatScalarDirectImageLimitCoherence to the pro-etale ringed morphism
of f, with constant and completed coefficient sheaves and exchangeScalar at both
ends. The scalar maps are flat by constant/completed equivalence. Restriction of
scalars leaves the underlying additive sheaves and ordinary limit projections
unchanged. Its exact flat left adjoint, also on strict towers, shows that the
same K-injective tower can be used after restriction. On that tower the ordinary
square is the identity on each section and each limit projection. The derived
scalar comparisons are fixed by their universal-unit equations: exchangeResPush
on towers and cbcRealizationResPush on individual objects. The constant-diagram
mates cbcRealizationResLimit have the same ordinary-limit normalization, by the
proved cbcRealizationLimit_mate_eq. The two direct-image/limit maps are the
conjugates of the constant/pullback square for the normalized adjunctions, hence
have the direct-image/limit derived-unit normalization. The first conclusion of
flatScalarDirectImageLimitCoherence is the displayed equation. Naturality
extends it from K-injective representatives to all derived strict towers. This
argument also applies to the zero tower, the empty scheme, and identity f. -/
theorem strictTowerScalarPushLimitCoherence {U T : Scheme.{t}} (f : U ⟶ T)
    (M : DerivedCategory (exchangeTowers U (d.completedRing U))) :
    (cbcRealizationRes d T).mapDerivedCategory.map
        ((d.directImageRlimIso f).hom.app M) ≫
      (cbcRealizationResLimit d T).hom.app ((d.towerPush f).obj M) ≫
      (completedRlim T (exchangeConstantRing T A)).map
        ((exchangeResPush d f).hom.app M) =
    (cbcRealizationResPush d f).hom.app ((completedRlim U (d.completedRing U)).obj M) ≫
      (ProEtale.StrictTower.moduleDirectImage A f).rightDerivedFunctor.map
        ((cbcRealizationResLimit d U).hom.app M) ≫
      (cbcRealizationPushLimit (A := A) f).hom.app ((exchangeTowerRes d U).obj M) := by
  sorry

end AlgebraicGeometry.Scheme
