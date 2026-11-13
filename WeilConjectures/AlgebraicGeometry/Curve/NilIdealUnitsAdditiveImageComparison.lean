/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

import WeilConjectures.AlgebraicGeometry.Curve.NilIdealUnitImageRelativeKernel
import WeilConjectures.AlgebraicGeometry.Curve.IdealAdditiveImageRelativeKernel
import WeilConjectures.AlgebraicGeometry.Curve.SquareZeroRelativeUnitsAdditiveKernel

/-! # Linearizing the unit image into the additive image
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- For a nil ideal I with I squared contained in J contained in I, subtracting one
identifies the multiplicative image of the congruence subgroup with the additive
image of the ideal. This assertion involves only structure rings and their units,
not the module cokernel or tensor sections. -/
theorem nonempty_nilIdealUnitsAdditiveImageIso (X : Scheme.{u})
    (I J : X.IdealSheafData) (hJI : J ≤ I) (hII : I * I ≤ J)
    (hIN : I ≤ X.nilradical) :
    Nonempty (image (kernel.ι (gmSheafToLowerStarGmSheaf I.subschemeι) ≫
        gmSheafToLowerStarGmSheaf J.subschemeι) ≅
      image (kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) ≫
        etaleAdditiveSheafToLowerStar J.subschemeι)) := by
  obtain ⟨eUnits⟩ := nonempty_nilIdealUnitImageRelativeKernelIso X I J hJI hIN
  obtain ⟨eAdditive⟩ := nonempty_idealAdditiveImageRelativeKernelIso X I J hJI
  obtain ⟨eRelative⟩ := nonempty_squareZeroRelativeUnitsAdditiveKernelIso X I J hJI hII
  exact ⟨eUnits ≪≫
    (Etale.lowerStar AddCommGrpCat.{u + 1} J.subschemeι).mapIso eRelative ≪≫
      eAdditive.symm⟩

end AlgebraicGeometry.Scheme
