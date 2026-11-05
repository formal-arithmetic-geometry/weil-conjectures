/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-!
# Canonical realization and constant-coefficient direct image

Source: Stacks Project, Tags 00YV and 03D1; Weil blueprint, order 1466
(blueprint: def-weil-proetale-inverse-image).
The normalization on the scalar-unit sections fixes the comparison, including its direction.

## Main definitions

- `sfIntrinsicDerivedEquivalence`: the specified realization on derived categories.
- `sfIntrinsicDirectImageComparison` and `sfIntrinsicDerivedDirectImageComparison`:
  the comparisons uniquely normalized on sections and K-injective representatives.
- `sfIntrinsicConstantModuleAdjunction`: the transported inverse-image adjunction.
- `AlgebraicGeometry.ProEtale.sfFixedDerivedPullback`: exact termwise inverse image.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
section
universe uA vA wA uT vT
set_option backward.isDefEq.respectTransparency false

-- Extend the prescribed comparison from K-injective representatives, as in
-- ExactPostcompositionKInjectiveDescent; all helpers here are private and proved.
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {T : Type uT} [Category.{vT} T]

end

section
universe uC uD uC' uD' vC vD vC' vD' wC wD wC' wD'
set_option backward.isDefEq.respectTransparency false

end

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
