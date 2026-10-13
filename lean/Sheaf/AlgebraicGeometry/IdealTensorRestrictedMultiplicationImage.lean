/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections

/-! # Image of multiplication restricted to an ideal multiple of a tensor product

Source: Stacks Project, Tag 01YB, last displayed map in the proof.
(blueprint: lem-pc-ideal-tensor-restricted-multiplication-image)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- The image of I^m times tensor multiplication is the higher ideal product.
Source: Stacks Project, Tag 01YB, last displayed map; affine product and tensor
comparisons in Tags 01I8 and 01AH.
(blueprint: lem-pc-ideal-tensor-restricted-multiplication-image)

Proof: Put T = I^n tensor H and let μ be multiplication. On each affine open U,
the tensor comparison identifies its sections with I(U)^n tensor H(U).
The recursive ideal power at m has inclusion range I(U)^m, also for m=0.
The affine product theorem gives the inclusion range I(U)^m T(U). Multiplication
maps this onto I(U)^m I(U)^n H(U) = I(U)^(n+m) H(U): one inclusion follows from
linearity, the reverse from writing ideal products as sums of products and lifting
each pure product to a tensor. The affine image theorem identifies the image of
the composite with this range. The ideal-sheaf-data product at n+m has the same
range. Both inclusions are monomorphisms. Equality of ranges on the affine basis
gives inverse factorizations between the subsheaves, since the unique local
preimages agree on overlaps and glue. These give e, with the required inclusion
identity. No Noetherianity or finiteness is needed. At either exponent zero the
same affine formula uses the unit ideal; zero ideals and zero H give zero images. -/
theorem ideal_tensor_restricted_multiplication_image
    {X : Scheme.{u}} (I : X.IdealSheafData) (H : X.Modules)
    [H.IsQuasicoherent] (n m : ℕ) :
    letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    let T := (I ^ n).toModules ⊗ H
    let μ := (I ^ n).toModulesι ▷ H ≫ (λ_ H).hom
    let j := idealModuleProductι (idealSheafPower I.toModulesι m).2 T
    ∃ e : idealModuleProduct (I ^ (n + m)).toModulesι H ≅ image (j ≫ μ),
      e.hom ≫ image.ι (j ≫ μ) = idealModuleProductι (I ^ (n + m)).toModulesι H := by sorry

end AlgebraicGeometry.Scheme.Modules
