/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.RankOne.PurityRankOneLocalData
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine
import WeilConjectures.SmoothPurity.PurityFiniteSetting.RankOne.RankOneKummerGenerator
import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
import WeilConjectures.CategoryTheory.RightDerivedZeroTransformation
import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement

/-! # Ordinary finite-coefficient Kummer calculation

## References

* [J. S. Milne, *Lectures on Étale Cohomology*, Proposition 14.3 and Example 16.3]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.RankOne

attribute [local implicit_reducible]
  HomologicalComplex.homologyFunctor

open AlgebraicGeometry.Scheme

end WeilConjectures.PurityFiniteSetting.RankOne
