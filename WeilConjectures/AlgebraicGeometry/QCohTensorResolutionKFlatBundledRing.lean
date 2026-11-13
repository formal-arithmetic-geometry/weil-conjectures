/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionAffineModel

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The affine K-flat theorem, stated with its ring kept bundled (Stacks, Tag 08DV). -/
theorem tensorResolution_isKFlat_bundledRing
    (A : CommRingCat.{u}) (M : ModuleCat.{u} A) (P : ProjectiveResolution M) :
    CochainComplex.IsKFlatTensor (R := (Spec A).sheaf)
      (((tilde.functor A).mapHomologicalComplex (.up ℤ)).obj
        (P.complex.extend ComplexShape.embeddingDownNat)) := by
  cases A
  exact tensorResolution_isKFlat _ M P

end AlgebraicGeometry
