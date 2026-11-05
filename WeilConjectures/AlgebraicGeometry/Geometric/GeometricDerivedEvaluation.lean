/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryRealization
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricCoefficientPullback
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricEvaluationMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Derived evaluation and coefficient comparison for a fixed ordinary realization

Source: Zheng Construction 4.1, the paragraph preceding Lemma 4.10 and Lemma 4.10.
(blueprint: lem-coef-semilinear-geometric-derived-evaluation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)

variable (A : Data.{c, v, r} J B τ)
  (O : GeometryOrdinary.{c, v, r} J B τ J' uInv uPush adjSet)
  (target : Data.{c, v, r} J' O.coefficients O.coefficientTransition)
  [∀ n : ℕ, Abelian.HasKInjectiveResolutions (Mod.{c, v, max c v r} J' (O.coefficients n))]
  [Abelian.HasKInjectiveResolutions
    (Systems.{c, v, max c v r} J' O.coefficients O.coefficientTransition)]

end WeilConjectures.SemilinearSections
