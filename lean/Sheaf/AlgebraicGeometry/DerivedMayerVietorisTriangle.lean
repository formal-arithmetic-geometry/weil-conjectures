/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import Sheaf.Algebra.Homology.KInjectiveRestrictOpen
import Sheaf.AlgebraicGeometry.DerivedCategory
import Sheaf.AlgebraicGeometry.InjectiveRestrictionSurjective
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions

/-! # Derived Mayer--Vietoris for a qcqs scheme

Source: Stacks Project, Cohomology, Tag 08BV; Derived Categories of Schemes, Tag 08D5
(blueprint: lem-pc-derived-mayer-vietoris-triangle).
-/

@[expose] public section

universe u₁ w₁

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048

/-- A two-open cover gives the direct-image Mayer--Vietoris distinguished triangle.
Source: Stacks Project, Tags 08BV and 08D5
(blueprint: lem-pc-derived-mayer-vietoris-triangle).

Proof:
1. Choose a K-injective resolution with injective terms
   (prop-pur-kinjective-resolutions-exist). Its restrictions remain K-injective
   (lem-sc-derived-k-injective-restrict-open), and compute the derived direct images
   (def-pc-derived-direct-image).
2. The sheaf gluing axiom gives exactness at the first two terms of the sectionwise
   sequence. Injectivity gives surjectivity of the difference of restriction maps
   (lem-sc-ringed-space-injective-restriction-surjective). This holds in every degree.
3. Apply the non-split short-exact-sequence triangle
   (lem-weil-pbc-complex-ses-triangle), and transport along the resolution isomorphism.
   The first map is the pair of units and the second is the difference of restrictions.
4. Restriction preserves quasi-coherent cohomology. Each open immersion is qcqs, so
   lem-pc-derived-direct-image-preserves-qcoh places the three direct-image terms in
   D_QCoh. Their biproduct and the triangle therefore lie in that full subcategory. -/
theorem schemeDerived_mayerVietoris_triangle
    (X : Scheme.{u₁}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E) :
    ∃ (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
      (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
      (adjUV : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣
        schemeDerivedDirectImage (U ⊓ V).ι)
      (δ : (schemeDerivedDirectImage (U ⊓ V).ι).obj
        ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj E) ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk (biprod.lift (adjU.unit.app E) (adjV.unit.app E))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left) adjU adjUV E)
          (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right) adjV adjUV E)))
        δ ∈ distTriang (schemeDerivedCategory X) ∧
      schemeDerivedQCohProperty X
        ((schemeDerivedDirectImage U.ι).obj
          ((schemeOpenRestriction X U).mapDerivedCategory.obj E)) ∧
      schemeDerivedQCohProperty X
        ((schemeDerivedDirectImage V.ι).obj
          ((schemeOpenRestriction X V).mapDerivedCategory.obj E)) ∧
      schemeDerivedQCohProperty X
        ((schemeDerivedDirectImage (U ⊓ V).ι).obj
          ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj E)) := by
  sorry

end AlgebraicGeometry
