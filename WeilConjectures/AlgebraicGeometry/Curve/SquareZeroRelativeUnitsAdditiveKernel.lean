/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Curve.SquareZeroRelativeSectionKernel
import WeilConjectures.AlgebraicGeometry.Curve.SquareZeroUnitsAdditiveKernelOfSections

/-! # A square-zero closed immersion identifies its unit and additive kernels.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- A square-zero closed immersion identifies its unit and additive kernels. -/
theorem nonempty_squareZeroRelativeUnitsAdditiveKernelIso (X : Scheme.{u})
    (I J : X.IdealSheafData) (hJI : J ≤ I) (hII : I * I ≤ J) :
    Nonempty (kernel (gmSheafToLowerStarGmSheaf (IdealSheafData.inclusion hJI)) ≅
      kernel (etaleAdditiveSheafToLowerStar (IdealSheafData.inclusion hJI))) := by
  apply nonempty_unitsAdditiveKernelIso_of_sections (IdealSheafData.inclusion hJI)
  intro V a b ha hb
  exact squareZeroRelativeSectionKernel X I J hJI hII V a b ha hb

end AlgebraicGeometry.Scheme
