/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometry.SemilinearGeometryOps
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricDerivedEvaluation
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricTensorLocalization
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSystemsExistence
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricCoefficientTower
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Existence of the geometric operation data

Source: Zheng Construction 4.1 and Lemma 4.10.
(blueprint: lem-coef-semilinear-geometric-operations-base-existence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits SheafOfModules
namespace CategoryTheory.Adjunction

end CategoryTheory.Adjunction

namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

end WeilConjectures.SemilinearSections
