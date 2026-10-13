/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
public import Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsRightExact

/-! # Tensor ideal identifications compatible with inclusion
(blueprint: lem-sc-etale-ideal-kernel-iso)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- Tensor sections identify with additive ideal kernels, compatibly with nested inclusion.
Source: blueprint `lem-sc-brauer-zero-all-curves`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-etale-ideal-kernel-iso)

Proof: Cover an etale object by affine etale objects V over affine opens U=Spec A.
Write B=Gamma(V,O). Flatness of B over A identifies B tensor I(U) and B tensor J(U)
with the extended ideals I_B and J_B. Restriction to the closed subscheme of either
ideal is the quotient map from B, so these extended ideals are its additive kernels.
The specified ideal modules are kernels of structure-module restriction, hence their
sections and inclusion agree with these ordinary ideals and inclusion. The resulting
isomorphisms commute with all affine restrictions, since tensor base change, quotient
and ideal inclusion commute with ring maps. Glue over affine refinements, sheafify,
and lift additive universes. The inclusion compatibility is checked on the same cover.
For I=J it is the identity; for J=0 both sides of the compatibility are zero. -/
theorem exists_etaleIdealKernelIsoPair (X : Scheme.{u})
    (I J : X.IdealSheafData) (hJI : J ≤ I) :
    ∃ eI : (Modules.etaleTensorSectionsFunctor X).obj I.toModules ≅
        kernel (etaleAdditiveSheafToLowerStar I.subschemeι),
      ∃ eJ : (Modules.etaleTensorSectionsFunctor X).obj J.toModules ≅
          kernel (etaleAdditiveSheafToLowerStar J.subschemeι),
        (Modules.etaleTensorSectionsFunctor X).map (IdealSheafData.toModulesOfLE hJI) ≫
            eI.hom ≫ kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) =
          eJ.hom ≫ kernel.ι (etaleAdditiveSheafToLowerStar J.subschemeι) := by sorry

end AlgebraicGeometry.Scheme
