/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesCoimageImageAffine
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleIsomorphismLocal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-! # CoherentFormalModulesCoimageImage

Source: Stacks Project, Lemma 087X.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical coimage-image comparison for coherent adic systems is invertible,
for any choices of the kernel and cokernel structures (Stacks, Tag 087X). -/
theorem coherentFormalModules_coimageImage_isIso (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) [HasKernels (CoherentFormalModule X I)]
    [HasCokernels (CoherentFormalModule X I)]
    {F G : CoherentFormalModule X I} (α : F ⟶ G) :
    IsIso (Abelian.coimageImageComparison α) := by
  exact (coherentFormalModule_isIso_of_isIso_restrict I
    (fun U : X.affineOpens ↦ (U : X.Opens)) (iSup_affineOpens_eq_top X)
    (Abelian.coimageImageComparison α)
    (fun U n ↦ coherentFormalModules_coimageImage_isIso_restrict_affine X I U α n)).1

end AlgebraicGeometry
