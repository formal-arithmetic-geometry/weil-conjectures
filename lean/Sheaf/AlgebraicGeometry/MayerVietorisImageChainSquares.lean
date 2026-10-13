/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.MayerVietorisImageChainData

/-! # Explicit restriction-induced comparison maps

Source: Stacks Project, Tags 08FE and 08BV.
(blueprint: def-pc-mayer-vietoris-image-chain-data).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian

/-- The explicit image components commute with the pair of units and the
restriction difference. Source: Stacks Tags 08FE and 08BV.
(blueprint: lem-pc-mayer-vietoris-image-chain-squares).

Proof: On a test open A, the comparison is the identity identifying
I(h⁻¹(A ∩ W)) with I(h⁻¹(A) ∩ h⁻¹(W)); scalar actions agree by the
restriction formula for h-sharp. It commutes with restrictions to smaller
opens. Thus h_* of each restriction unit, followed by the comparison and
restriction of f, is f followed by the corresponding restriction unit of J.
The two components give the first square by the biproduct universal property.
The same naturality for U ∩ V ⊆ U and U ∩ V ⊆ V gives the second square;
additivity preserves its minus sign. The sectionwise calculation uses only
functorial restriction, so also applies to empty and repeated opens. -/
theorem schemeMV_image_chain_squares
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U V : Y.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).obj I ⟶ J) :
    let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)
    let b := biprod.lift
      (F.map biprod.fst ≫ schemeMVImageComponent h U I J f)
      (F.map biprod.snd ≫ schemeMVImageComponent h V I J f)
    (F.map (schemeMayerVietorisF X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) I) ≫ b =
      f ≫ schemeMayerVietorisF Y U V J) ∧
    (F.map (schemeMayerVietorisG X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) I) ≫
        schemeMVImageComponent h (U ⊓ V) I J f =
      b ≫ schemeMayerVietorisG Y U V J) := by
  sorry

end AlgebraicGeometry
