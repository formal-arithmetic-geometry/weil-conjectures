/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesCoimageImageRestrictAffineMono
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesCoimageImageRestrictAffineEpi

/-! # Affine-local coimage-image comparison

## References

* Stacks Project, Tags 087W and 087X
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- On one affine open and at one positive level, the coimage-image comparison
of coherent formal modules restricts to an isomorphism of module sheaves
(Stacks, Tags 087X and 087W). -/
theorem coherentFormalModules_coimageImage_isIso_restrict_affine
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    [HasKernels (CoherentFormalModule X I)]
    [HasCokernels (CoherentFormalModule X I)] (U : X.affineOpens)
    {F G : CoherentFormalModule X I} (α : F ⟶ G) (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor (U : X.Opens).ι).map
      ((Abelian.coimageImageComparison α).hom.app (op n))) := by
  let φ := (Scheme.Modules.restrictFunctor (U : X.Opens).ι).map
    ((Abelian.coimageImageComparison α).hom.app (op n))
  have : Mono φ := coherentFormalModules_coimageImage_isMono_restrict_affine X I U α n
  have : Epi φ := coherentFormalModules_coimageImage_isEpi_restrict_affine X I U α n
  exact isIso_of_mono_of_epi φ

end AlgebraicGeometry
