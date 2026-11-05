/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometry.SemilinearGeometryOps
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOperationsBaseExistence
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOperationsTransitionExistence

/-! # Normalized geometric operations on semilinear systems

Source: Zheng Construction 4.1 and Lemma 4.10. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe c v r
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

end WeilConjectures.SemilinearSections
