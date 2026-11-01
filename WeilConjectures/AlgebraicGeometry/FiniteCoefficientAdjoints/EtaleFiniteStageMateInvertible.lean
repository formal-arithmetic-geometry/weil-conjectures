/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointData
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.EtaleFiniteStageMateClosed
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.EtaleFiniteStageMateLocality

/-! # Invertibility of the ordinary etale finite-stage exceptional mate

Source: the ordinary etale argument of lem-pur-finite-coefficient-adjoint-comparisons,
steps 8--12, and current blueprint reduction-exceptional, Locality and Charts.
(blueprint: lem-pur-etale-finite-stage-mate-invertible).
-/

@[expose] public noncomputable section
set_option autoImplicit false
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

end AlgebraicGeometry.FiniteCoefficientAdjoints
