/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.Topology.OpenModuleCohomology
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.Paper.HigherDirectImagePresheaf
import Sheaf.Topology.RestrictInjectiveResolution

/-! # Vanishing of higher direct image on an affine neighbourhood basis

Source: Stacks Project, Tags 01E4 and 01E1.
(blueprint: lem-pc-higher-direct-image-affine-basis-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Vanishing of cohomology on inverse images of affine opens of U implies vanishing
of the p-th higher direct image restricted to U. No quasi-coherence is required.
Source: Stacks Project, Tag 01E4 (sheafified cohomology presheaf) and Tag 01E1
(restriction of injective resolutions).
(blueprint: lem-pc-higher-direct-image-affine-basis-vanishing).

Proof: Restrict an injective resolution of F to f^{-1}U. It remains injective and
computes the open cohomology of the restricted coefficient module. Higher direct
image commutes with open restriction, by this same restricted resolution. Tag 01E4
identifies it with the sheafification of the presheaf V maps to H^p(g^{-1}V,F|_Y),
where Y=f^{-1}U and g=f|_U. Every point of U has an affine neighbourhood basis and
all these presheaf values are zero by the hypothesis. Its stalks, the filtered
colimits of these values, are zero; sheafification preserves stalks. Thus every
stalk of the restricted higher direct image is zero, and the module sheaf is zero.
This includes degree zero, empty U, and empty inverse images. -/
theorem isZero_restrict_higherDirectImage_of_affine_basis
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (F : X.Modules) (p : ℕ)
    (h : ∀ (V : U.toScheme.Opens), IsAffineOpen V →
      IsZero ((RingedSpace.openModuleCohomology (f ⁻¹ᵁ U).toScheme.toRingedSpace p
        ((f ∣_ U) ⁻¹ᵁ V)).obj (Scheme.Modules.restrict F (f ⁻¹ᵁ U).ι))) :
    IsZero (Scheme.Modules.restrict
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj F) U.ι) := by sorry

end AlgebraicGeometry
