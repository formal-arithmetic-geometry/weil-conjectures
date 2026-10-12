/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum
import Sheaf.Paper.HigherDirectImagePresheaf

/-! # Surjectivity of ordinary higher direct image on coproducts

Source: Stacks Project, Tag 07TB, with Tags 01FF and 01FE.
(blueprint: lem-pc-module-higher-direct-image-coproduct-epi).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Ordinary higher direct image sends a module-sheaf coproduct cofan to a jointly
surjective family. No quasi-coherence hypothesis is needed.
Source: Stacks Project, Tag 07TB, proof using cohomology on inverse images of affine
opens, with Tags 01FF and 01FE.
(blueprint: lem-pc-module-higher-direct-image-coproduct-epi).

Proof: Restriction to an open subspace preserves coproducts of module sheaves, since
it is left adjoint to direct image for the open immersion. For an affine open V of Y,
its inverse image under f is quasi-compact and quasi-separated. The cohomology
coproduct theorem on this inverse image says that every class with coefficients in
the restricted coproduct is a finite sum of classes coming from its summands.
This theorem applies to all module sheaves, not only quasi-coherent ones.
Compute the ordinary higher direct images with injective resolutions. Their
cohomology presheaves have values H^p(f^{-1}(V), -); the canonical maps from these
presheaves to the higher direct image sheaves induce isomorphisms after
sheafification, naturally in the coefficient module. Thus every germ in the target
higher direct image is represented, on some affine neighborhood, by a cohomology
class on its inverse image. Express this class as a finite sum as above. Each
summand class maps to a section of the corresponding higher direct image; their
finite sum lifts the original germ through the sheaf coproduct comparison.
Consequently the comparison is surjective on every stalk. A map of module sheaves
surjective on stalks is epic, proving the assertion. For an empty family, its
coproduct is zero and additivity makes the target zero; for p = 0 this is the same
argument with ordinary sections. Naturality of the resolution comparison identifies
the maps from summands with the displayed rightDerived functor maps. -/
theorem moduleHigherDirectImage_coproduct_epi
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (I : Type u) (M : I → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (N : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ι : ∀ i, M i ⟶ N)
    (hc : IsColimit (Cofan.mk N ι)) (p : ℕ) :
    Epi (Sigma.desc (fun i ↦
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).map (ι i))) := by
  sorry

end AlgebraicGeometry
