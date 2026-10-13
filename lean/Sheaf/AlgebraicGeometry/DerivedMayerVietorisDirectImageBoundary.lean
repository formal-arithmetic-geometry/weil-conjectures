/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData

/-! # DerivedMayerVietorisDirectImageBoundary

Source: Stacks Project, Cohomology, Tags 08BV and 0D5T; Derived Categories of Schemes,
Tag 0DJ9 (blueprint: lem-pc-derived-mayer-vietoris-direct-image-boundary).
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

/-- The explicitly constructed boundary commutes with the recorded direct-image comparisons.
Source: Stacks Tags 08BV, 0D5T and 0DJ9
(blueprint: lem-pc-derived-mayer-vietoris-direct-image-boundary).

Proof:
1. Use the fixed K-injective representative I of E with injective terms. Its concrete
   Mayer--Vietoris sequence is short exact and split in each degree, since its first
   term is injective. Its other terms are K-injective: restriction preserves this
   property, open direct image is right adjoint to exact restriction, and biproducts
   of K-injective complexes are K-injective.
2. Apply the termwise-split short-exact-sequence triangle comparison for h_*.
   It identifies the image boundary, including the commutation with shift, with the
   boundary of the termwise image sequence.
3. Resolve h_*I by a K-injective complex J with injective terms. The resolution map
   and its restrictions induce a map from the image sequence to the Mayer--Vietoris
   sequence of J. The intersection component is the direct-image composition followed
   by the inverse open-restriction comparison, by their K-injective computation formulas.
4. Apply triangleOfSESδ_naturality to this map of short exact sequences. Compose with
   the resolution isomorphisms and the explicit intersection comparisons used in
   schemeMVBoundary. Cancel the computation isomorphisms. Naturality of these comparisons
   and of commutation with shift gives the displayed equation for E. No assertion
   about the other two triangle squares is used here.
-/
theorem schemeMV_directImage_boundary
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U V : Y.Opens)
    (hcover : U ⊔ V = ⊤)
    (hcover' : (h ⁻¹ᵁ U) ⊔ (h ⁻¹ᵁ V) = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) :
    (schemeMVImageTriangle h
      (schemeMVTriangle X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) hcover' E)).mor₃ =
      (schemeMVOpenComparison h (U ⊓ V) E).hom ≫
        schemeMVBoundary Y U V hcover ((schemeDerivedDirectImage h).obj E) := by
  sorry

end AlgebraicGeometry
