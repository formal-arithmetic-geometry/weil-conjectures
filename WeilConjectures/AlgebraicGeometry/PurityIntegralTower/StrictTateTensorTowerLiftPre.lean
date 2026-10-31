/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.CondensedTateIntegralTowerData
import all WeilConjectures.AlgebraicGeometry.CompletedLisse.LisseCompletedPointwiseComparison
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCanonicalTruncations
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootLocalModels

/-! A pre-tower for the strict ordinary Tate quotient construction.

The cocycle equation is kept separate from the other fields so that the
construction and its coherence can be proved independently.
(blueprint: lem-pur-strict-tate-tensor-tower-data-pre)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

structure StrictTateTensorTowerPre (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) where
  tower : DerivedCategory (pbcTowers T (pbcAdicCompletion T d))
  level : ∀ n : ℕ, DerivedCategory (pbcModules T ((pbcAdicRings T d).obj (op n)))
  evaluation : ∀ n : ℕ,
    (pbcDerivedRestrict (pbcAdicProjection T d n)).obj (level n) ≅
      (pbcTowerEvaluation T (pbcAdicCompletion T d) n).obj tower
  normalization : ∀ (b a : ℕ) (hab : a ≤ b),
    (pbcDerivedExtend (pbcAdicQuotient T d b a hab)).obj (level b) ≅ level a
  transition : ∀ (b a : ℕ) (hab : a ≤ b),
    (pbcDerivedRestrict (pbcAdicProjection T d b)).map
        (adicTowerSemilinearTransition T d level normalization b a hab) ≫
      (pbcDerivedRestrictComp (pbcAdicProjection T d b)
        (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
        (pbcAdicProjection_comp T d b a hab)).hom.app (level a) ≫
      (evaluation a).hom =
    (evaluation b).hom ≫
      (pbcTowerTransition T (pbcAdicCompletion T d) b a hab).app tower

def StrictTateTensorTowerPre.Cocycle
    {T : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    {d : AdicCoefficientDatum A} (P : StrictTateTensorTowerPre T d) : Prop :=
  ∀ (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c),
    adicTowerSemilinearTransition T d P.level P.normalization c a
        (hab.trans hbc) =
      adicTowerSemilinearTransition T d P.level P.normalization c b hbc ≫
        (pbcDerivedRestrict (pbcAdicQuotient T d c b hbc)).map
          (adicTowerSemilinearTransition T d P.level P.normalization b a hab) ≫
        (pbcDerivedRestrictComp (pbcAdicQuotient T d c b hbc)
          (pbcAdicQuotient T d b a hab)
          (pbcAdicQuotient T d c a (hab.trans hbc))
          (pbcAdicQuotient_comp T d c b a hab hbc)).hom.app (P.level a)

attribute [local irreducible] HasDerivedCategory.standard completedAdicChangeData

set_option linter.unusedVariables false in
end AlgebraicGeometry.Scheme.PurityIntegralTower
