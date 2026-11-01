/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSmoothPullbackExchange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionUnshiftedPullbackCube
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionPullbackComparisonShift

/-! # Finite scalar extension and the shifted ordinary pullback square

Source: blueprint finite-reduction-of-purity proof, Steps 2 and 4.
(blueprint: lem-pur-finite-reduction-shifted-pullback-cube)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

private def comparisonNatIso (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P.finiteReductionPullback f ⋙ P.finiteReduction m hm hmn X ≅
      P.finiteReduction m hm hmn Y ⋙
        (P.finiteReductionSetting m hm).finiteReductionPullback f :=
  Functor.isoWhiskerRight (P.finiteReductionRawPullbackModel f).symm
      (P.finiteReduction m hm hmn X) ≪≫
    (Scheme.proEtaleReductionPullbackIso f
      (Scheme.proEtaleConstantRing Y P.Ring)
      (Scheme.proEtaleConstantRing Y (P.finiteReductionSetting m hm).Ring)
      (Scheme.proEtaleConstantRing X P.Ring)
      (Scheme.proEtaleConstantRing X (P.finiteReductionSetting m hm).Ring)
      (Scheme.proEtaleConstantRingMap (T := Y) (P.finiteReductionRingHom m hm hmn))
      (Scheme.proEtaleConstantRingMap (T := X) (P.finiteReductionRingHom m hm hmn))
      (Scheme.proEtaleConstantRingComparison f P.Ring)
      (Scheme.proEtaleConstantRingComparison f (P.finiteReductionSetting m hm).Ring)
      (P.finiteReductionCoefficientSquare m hm hmn f)).symm ≪≫
    Functor.isoWhiskerLeft (P.finiteReduction m hm hmn Y)
      ((P.finiteReductionSetting m hm).finiteReductionRawPullbackModel f)

end WeilConjectures.PurityFiniteSetting
