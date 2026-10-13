/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisData

/-! # Ordinary direct-image comparison squares for Mayer--Vietoris

Source: Stacks Project, Cohomology, Tags 08BV and 08FE.
(blueprint: lem-pc-mayer-vietoris-direct-image-chain-squares).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

/-- A supplied chain map out of direct image extends to the three open terms,
commuting with the two units and the two unsigned restrictions.
Source: Stacks Project, Tag 08BV (lemma-exact-sequence-j-star), displayed complex;
Tag 08FE (lemma-restrict-direct-image-open), the underived sectionwise identity.
(blueprint: lem-pc-mayer-vietoris-direct-image-chain-squares).

Proof: For each open A of Y, identify h_* j_{h^{-1}A,*}(I|h^{-1}A) with
j_{A,*}((h_*I)|A). In degree n over a test open B of Y both are I^n evaluated
on h^{-1}(B intersect A). The equality h^{-1}(B intersect A) =
h^{-1}B intersect h^{-1}A gives this identification; the ring action agrees
by functoriality of the scheme structure-sheaf map. Transport the ordinary
restriction functors through Scheme.Modules.overFunctorEquiv, as in the fixed
adjunction defining schemeOpenModuleImage. These section identifications
commute with differentials and are natural in I. Compose them with the open
image of the supplied chain map f, for A = U, V and U intersect V.
On sections the first two asserted squares say that f commutes with restriction
from B to B intersect A. This is the naturality of the module-sheaf morphism f
in each degree. The last two squares say the same for restriction from B
intersect U or B intersect V to B intersect U intersect V. The mate definition
of schemeOpenModuleImageRestriction is this restriction: the nested restriction
comparison identifies restriction twice, and the adjunction counit cancels
the repeated restriction. Equality of section maps in every degree gives the
four chain-map identities. There is no cover, injectivity, localization or
derived-resolution assumption. Empty opens, repeated opens and zero complexes
use the same section identities. -/
theorem schemeMV_directImage_chain_squares
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U V : Y.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) :
    let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)
    ∃ (a : F.obj (schemeOpenModuleImageComplex X (h ⁻¹ᵁ U) I) ⟶
        schemeOpenModuleImageComplex Y U J)
      (b : F.obj (schemeOpenModuleImageComplex X (h ⁻¹ᵁ V) I) ⟶
        schemeOpenModuleImageComplex Y V J)
      (c : F.obj (schemeOpenModuleImageComplex X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)) I) ⟶
        schemeOpenModuleImageComplex Y (U ⊓ V) J),
      f ≫ schemeOpenModuleImageComplexUnit Y U J =
        F.map (schemeOpenModuleImageComplexUnit X (h ⁻¹ᵁ U) I) ≫ a ∧
      f ≫ schemeOpenModuleImageComplexUnit Y V J =
        F.map (schemeOpenModuleImageComplexUnit X (h ⁻¹ᵁ V) I) ≫ b ∧
      a ≫ schemeOpenModuleImageComplexRestriction Y (homOfLE inf_le_left) J =
        F.map (schemeOpenModuleImageComplexRestriction X (homOfLE inf_le_left) I) ≫ c ∧
      b ≫ schemeOpenModuleImageComplexRestriction Y (homOfLE inf_le_right) J =
        F.map (schemeOpenModuleImageComplexRestriction X (homOfLE inf_le_right) I) ≫ c := by
  sorry

end AlgebraicGeometry
