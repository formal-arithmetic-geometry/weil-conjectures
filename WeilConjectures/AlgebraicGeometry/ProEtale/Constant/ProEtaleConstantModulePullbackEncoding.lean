/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement

/-!
# Pullback and restriction to constant scalars

Source: Stacks Project, Tags 093I and 03D3.
(blueprint: lem-weil-pbc-proetale-constant-module-pullback-encoding).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (B : Type u) [CommRing B]

end AlgebraicGeometry.Scheme
