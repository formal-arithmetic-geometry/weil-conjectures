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

/-- Normalized geometric operations on semilinear systems.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 06YY, 07A4, 07A6. -/
theorem semilinearGeometricOperations (systems : Data.{c, v, r} J B τ)
    {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush) [PreservesFiniteLimits uInv] :
    Nonempty {G : Geometry.{c, v, r} J B τ systems J' uInv uPush adjSet //
      G.PullTransitionFormula J B τ systems J' uInv uPush adjSet} := by
  obtain ⟨G⟩ := semilinearGeometryBaseExistence J B τ systems J' uInv uPush adjSet
  exact ⟨⟨G, semilinearGeometryTransitionExistence J B τ systems J' uInv uPush adjSet G⟩⟩

end WeilConjectures.SemilinearSections
