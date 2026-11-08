/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
public import Submission.WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
import Submission.WeilConjectures.AlgebraicGeometry.Lisse.Finite.LisseFiniteQuotientEtaleOriginCore
import Submission.WeilConjectures.AlgebraicGeometry.Pbc.PbcFinitePullbackConstructibility
import Submission.WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import Submission.WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import Submission.WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
import Submission.WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Single finite quotient origins and their conditional constant-model transport

Source: Stacks Project, Tags 09AL and 09B1, and coefficient transport in Tag 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

/-- One finite quotient descended to an etale chart. No point, normalization arrow,
or choice of a constant model is included. Transport accepts any supplied model.

Source: Stacks Project, proetale.tex, Tags 09AL, 09B1 and 09C6.
(blueprint: lem-weil-pbc-lisse-finite-quotient-etale-origin). -/
structure LisseFiniteQuotientEtaleOrigin
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (K : DerivedCategory (pbcModules X ((pbcAdicRings X d).obj (op n))))
    (V : Y.Etale) where
  level : DerivedCategory (Sheaf V.left.smallEtaleTopology
    (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
  lisse : ∀ q : ℤ, IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor _ q).obj level)
  vanishing : ∀ q : ℤ,
    IsZero ((DerivedCategory.homologyFunctor _ q).obj K) →
    IsZero ((DerivedCategory.homologyFunctor _ q).obj level)
  refinementLisse : ∀ (W : Y.ProEt) (_w : W ⟶ (toProEt Y).obj V) (q : ℤ),
    IsRelativelyFiniteLisseModule (W.hom ≫ g) (A ⧸ d.ideal ^ (n + 1))
      ((pbcRestrict ((adicTowerInverseImage (W.hom ≫ g)).map
        (pbcLevelConstantComparison X d n).hom)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((adicTowerPullback (W.hom ≫ g)
              ((pbcAdicRings X d).obj (op n))).obj K)))
  transport : ∀ (Z : V.left.Etale)
    (E : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))),
    Nonempty ((AlgebraicGeometry.Etale.upperStar _ Z.hom).mapDerivedCategory.obj level ≅
      (constantSheaf Z.left.smallEtaleTopology _).mapDerivedCategory.obj E) →
    ∀ (W : Y.ProEt) (_w : W ⟶ (toProEt Y).obj (Etale.mk (Z.hom ≫ V.hom))),
      Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
        (adicTowerPullback (W.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj K)

end AlgebraicGeometry.Scheme
