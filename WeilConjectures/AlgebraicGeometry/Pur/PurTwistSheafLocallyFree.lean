/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootLocalModels
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootTransitions
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistIntegralLocalModels
import WeilConjectures.AlgebraicGeometry.Completed.CompletedLineDerived
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistIntegralBasis
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientComparison
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleSingleSupport
import WeilConjectures.AlgebraicGeometry.Finite.FiniteLocallyFreeLineModels

/-! # Local freeness and derived completeness of the Tate line

Source: coefficient-twist blueprint, order 1505
(blueprint: lem-pur-twist-sheaf-locally-free).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
