/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointData
import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOrigin

/-! # Reflection of an exceptional coefficient mate through the site comparison

Source: current blueprint reduction-exceptional, site/coefficient compatibility;
parent lem-pur-finite-coefficient-adjoint-comparisons, steps 7--8 and 12--13.
(blueprint: lem-pur-normalized-change-site-reflection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
attribute [local instance 20000] CommRing.toRing Field.toCommRing DFunLike.toCoeFun
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.FiniteCoefficientAdjoints

attribute [-instance] CategoryTheory.catToReflQuiver in
end AlgebraicGeometry.FiniteCoefficientAdjoints
