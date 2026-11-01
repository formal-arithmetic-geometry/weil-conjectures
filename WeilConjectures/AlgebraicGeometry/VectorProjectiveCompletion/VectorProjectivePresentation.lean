/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.VectorProjectiveCompletion.VectorProjectiveCompletionData
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalGeometry
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
/-! # Presented projective bundle for O plus F

Source: Stacks Project, Constructions, Tags 01OA, 01OB and 01OE.
(blueprint: lem-amb-vector-projective-presentation). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.VectorProjectiveCompletion
private def symmetricCongr {R M N : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    SymmetricAlgebra R M ≃ₐ[R] SymmetricAlgebra R N :=
  AlgEquiv.ofAlgHom
    (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp e.toLinearMap))
    (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R M).comp e.symm.toLinearMap))
    (by ext m; simp) (by ext m; simp)
private theorem symmetricCongr_ι {R M N : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (m : M) :
    symmetricCongr e (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R N (e m) := by
  exact SymmetricAlgebra.lift_ι_apply _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
end AlgebraicGeometry.VectorProjectiveCompletion
