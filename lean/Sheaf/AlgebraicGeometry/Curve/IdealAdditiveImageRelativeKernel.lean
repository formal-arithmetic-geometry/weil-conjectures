/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # The additive ideal image is the pushforward of the relative additive kernel.

Source: blueprint `lem-sc-brauer-zero-all-curves`, Proof, Step 1 and its Claim;
the affine argument in `lem-sc-nil-ideal-units-additive-image-comparison`.
(blueprint: lem-sc-ideal-additive-image-relative-kernel)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- The additive ideal image is the pushforward of the relative additive kernel.
Source: blueprint `lem-sc-brauer-zero-all-curves`, Proof, Step 1 and its Claim;
the affine argument in `lem-sc-nil-ideal-units-additive-image-comparison`.
(blueprint: lem-sc-ideal-additive-image-relative-kernel)

Proof: Refine an etale X-scheme by affine opens lying over affine opens of X.
Write B for the structure ring and I_B,J_B for the extended ideals. The relative
additive kernel is the kernel of B/J_B to B/I_B, hence I_B/J_B. The additive
kernel before restriction is I_B, whose image in B/J_B is precisely I_B/J_B:
a class in the relative kernel has a representative in I_B. This description
commutes with restrictions. Pushforward preserves kernels, so the relative
kernel is a subobject of the additive functions on the J subscheme on X's
etale site. Its sections are locally exactly the sectionwise image of the
displayed composite. Sheafifying the presheaf image identifies the categorical
image with this subobject. Uniqueness of image factorizations yields the
isomorphism. This is independent of nilpotence and of I squared. In the cases
I=J, I=0, and the empty scheme the same descriptions give zero groups. -/
theorem nonempty_idealAdditiveImageRelativeKernelIso (X : Scheme.{u})
    (I J : X.IdealSheafData) (hJI : J ≤ I) :
    Nonempty (image (kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) ≫
        etaleAdditiveSheafToLowerStar J.subschemeι) ≅
      (Etale.lowerStar AddCommGrpCat.{u + 1} J.subschemeι).obj
        (kernel (etaleAdditiveSheafToLowerStar (IdealSheafData.inclusion hJI)))) := by sorry

end AlgebraicGeometry.Scheme
