/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
import Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle
import Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Functoriality of derived Mayer--Vietoris triangles

Source: Stacks Project, Cohomology, Tags 08BV and 0D5T; Derived Categories of Schemes,
Tag 0DJ9 (blueprint: lem-pc-derived-mayer-vietoris-functorial).
-/

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

/-- Mayer--Vietoris boundaries can be chosen simultaneously, naturally in the object.
The adjunction units and the difference of restrictions are the first two maps.
Source: Stacks, Tag 08BV (blueprint: lem-pc-derived-mayer-vietoris-functorial).

Proof:
1. Choose K-injective representatives with injective terms
   (prop-pur-kinjective-resolutions-exist). Restriction preserves K-injectivity
   (lem-sc-derived-k-injective-restrict-open). The Mayer--Vietoris sequence is exact
   degreewise by injective restriction surjectivity
   (lem-sc-ringed-space-injective-restriction-surjective).
2. Represent derived morphisms by chain maps into K-injective representatives
   (lem-sc-kinjective-quasi-iso-comparison). Restriction gives a morphism of the
   short exact sequences. Naturality of triangleOfSES, including its boundary,
   gives the three commuting squares (lem-weil-pbc-complex-ses-triangle).
3. For direct image, apply the triangulated right derived functor
   (lem-pc-right-derived-functor-triangulated). Choose a K-injective representative
   J of h_*I' and a quasi-isomorphism h_*I' → J. Its restrictions give the
   comparison of the middle and intersection terms, using derived direct-image
   composition (lem-pc-derived-direct-image-composition) and open restriction
   (lem-pc-restrict-derived-direct-image-open).
4. The source sequence is degreewise split because I' has injective terms. Its
   other complexes are K-injective by restriction and the exact-left-adjoint
   criterion (lem-weil-pbc-right-adjoint-preserves-kinjective). Apply
   lem-pc-derived-functor-termwise-split-ses-triangle to identify the image
   boundary with the boundary of the image sequence. Naturality of triangleOfSES
   applied to q and its restrictions gives the final square, hence an isomorphism
   of distinguished triangles. Quasi-coherence of Rh_*E' follows from
   lem-pc-derived-direct-image-preserves-qcoh.
-/
theorem schemeDerived_mayerVietoris_naturality
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (U ⊓ V).toScheme.toRingedSpace))] :
    ∃ (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣
        schemeDerivedDirectImage U.ι)
      (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣
        schemeDerivedDirectImage V.ι)
      (adjUV : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣
        schemeDerivedDirectImage (U ⊓ V).ι)
      (δ : ∀ E : schemeDerivedCategory X,
        (schemeDerivedDirectImage (U ⊓ V).ι).obj
          ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj E) ⟶ E⟦(1 : ℤ)⟧),
      (∀ (E : schemeDerivedCategory X), schemeDerivedQCohProperty X E →
        Triangle.mk (biprod.lift (adjU.unit.app E) (adjV.unit.app E))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left)
            adjU adjUV E)
          (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right)
            adjV adjUV E))) (δ E) ∈ distTriang (schemeDerivedCategory X)) ∧
      ∀ (E F : schemeDerivedCategory X),
        schemeDerivedQCohProperty X E → schemeDerivedQCohProperty X F →
        ∀ φ : E ⟶ F,
          ∃ m : (Triangle.mk (biprod.lift (adjU.unit.app E) (adjV.unit.app E))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left)
            adjU adjUV E)
          (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right)
            adjV adjUV E))) (δ E)) ⟶
            (Triangle.mk (biprod.lift (adjU.unit.app F) (adjV.unit.app F))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left)
            adjU adjUV F)
          (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right)
            adjV adjUV F))) (δ F)),
            m.hom₁ = φ ∧
            m.hom₂ = biprod.map
              ((schemeDerivedDirectImage U.ι).map
          ((schemeOpenRestriction X U).mapDerivedCategory.map φ))
              ((schemeDerivedDirectImage V.ι).map
          ((schemeOpenRestriction X V).mapDerivedCategory.map φ)) ∧
            m.hom₃ = (schemeDerivedDirectImage (U ⊓ V).ι).map
          ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.map φ) := by
  sorry

/-- The image Mayer--Vietoris triangle is identified with the target one by
composition and open-restriction comparison isomorphisms, with identity first component.
The comparison functor isomorphisms are the recorded ones of
lem-pc-derived-direct-image-composition and lem-pc-restrict-derived-direct-image-open
(`Classical.choice` of `derivedDirectImageComposition` and
`schemeDerivedDirectImage_openRestriction`), the same for every object.
The triangle isomorphism includes compatibility with the connecting maps.
Source: Stacks, Tags 08BV, 0D5T and 0DJ9
(blueprint: lem-pc-derived-mayer-vietoris-functorial).

Proof:
1. Choose K-injective representatives with injective terms
   (prop-pur-kinjective-resolutions-exist). Restriction preserves K-injectivity
   (lem-sc-derived-k-injective-restrict-open). The Mayer--Vietoris sequence is exact
   degreewise by injective restriction surjectivity
   (lem-sc-ringed-space-injective-restriction-surjective).
2. Represent derived morphisms by chain maps into K-injective representatives
   (lem-sc-kinjective-quasi-iso-comparison). Restriction gives a morphism of the
   short exact sequences. Naturality of triangleOfSES, including its boundary,
   gives the three commuting squares (lem-weil-pbc-complex-ses-triangle).
3. For direct image, apply the triangulated right derived functor
   (lem-pc-right-derived-functor-triangulated). Choose a K-injective representative
   J of h_*I' and a quasi-isomorphism h_*I' → J. Its restrictions give the
   comparison of the middle and intersection terms, using derived direct-image
   composition (lem-pc-derived-direct-image-composition) and open restriction
   (lem-pc-restrict-derived-direct-image-open).
4. The source sequence is degreewise split because I' has injective terms. Its
   other complexes are K-injective by restriction and the exact-left-adjoint
   criterion (lem-weil-pbc-right-adjoint-preserves-kinjective). Apply
   lem-pc-derived-functor-termwise-split-ses-triangle to identify the image
   boundary with the boundary of the image sequence. Naturality of triangleOfSES
   applied to q and its restrictions gives the final square, hence an isomorphism
   of distinguished triangles. Quasi-coherence of Rh_*E' follows from
   lem-pc-derived-direct-image-preserves-qcoh.
-/
theorem schemeDerived_mayerVietoris_directImage
    (X Y : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (h : X ⟶ Y) [QuasiCompact h] [QuasiSeparated h]
    (U V : Y.Opens) (hU : IsCompact (U : Set Y)) (hV : IsCompact (V : Set Y))
    (hcover : U ⊔ V = ⊤)
    (hU' : IsCompact ((h ⁻¹ᵁ U) : Set X))
    (hV' : IsCompact ((h ⁻¹ᵁ V) : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    :
    ∃ (adjU : (schemeOpenRestriction Y U).mapDerivedCategory ⊣
        schemeDerivedDirectImage U.ι)
      (adjV : (schemeOpenRestriction Y V).mapDerivedCategory ⊣
        schemeDerivedDirectImage V.ι)
      (adjUV : (schemeOpenRestriction Y (U ⊓ V)).mapDerivedCategory ⊣
        schemeDerivedDirectImage (U ⊓ V).ι)
      (δ : ∀ E : schemeDerivedCategory Y,
        (schemeDerivedDirectImage (U ⊓ V).ι).obj
          ((schemeOpenRestriction Y (U ⊓ V)).mapDerivedCategory.obj E) ⟶ E⟦(1 : ℤ)⟧)
      (adjU' : (schemeOpenRestriction X (h ⁻¹ᵁ U)).mapDerivedCategory ⊣
        schemeDerivedDirectImage (h ⁻¹ᵁ U).ι)
      (adjV' : (schemeOpenRestriction X (h ⁻¹ᵁ V)).mapDerivedCategory ⊣
        schemeDerivedDirectImage (h ⁻¹ᵁ V).ι)
      (adjUV' : (schemeOpenRestriction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))).mapDerivedCategory ⊣
        schemeDerivedDirectImage ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)).ι)
      (δ' : ∀ E : schemeDerivedCategory X,
        (schemeDerivedDirectImage ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)).ι).obj
          ((schemeOpenRestriction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))).mapDerivedCategory.obj E) ⟶ E⟦(1 :
            ℤ)⟧),
      (∀ (E F : schemeDerivedCategory X),
        schemeDerivedQCohProperty X E → schemeDerivedQCohProperty X F →
        ∀ φ : E ⟶ F,
          δ' E ≫ φ⟦(1 : ℤ)⟧' =
            (schemeDerivedDirectImage ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)).ι).map
              ((schemeOpenRestriction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))).mapDerivedCategory.map φ) ≫ δ' F) ∧
      (∀ (E F : schemeDerivedCategory Y),
        schemeDerivedQCohProperty Y E → schemeDerivedQCohProperty Y F →
        ∀ φ : E ⟶ F,
          δ E ≫ φ⟦(1 : ℤ)⟧' =
            (schemeDerivedDirectImage (U ⊓ V).ι).map
              ((schemeOpenRestriction Y (U ⊓ V)).mapDerivedCategory.map φ) ≫ δ F) ∧
      ∀ (E : schemeDerivedCategory X), schemeDerivedQCohProperty X E →
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage h).obj E) ∧
      (Triangle.mk (biprod.lift (adjU'.unit.app E) (adjV'.unit.app E))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left)
            adjU' adjUV' E)
          (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right)
            adjV' adjUV' E))) (δ' E)) ∈ distTriang (schemeDerivedCategory X) ∧
      (Triangle.mk (biprod.lift (adjU.unit.app ((schemeDerivedDirectImage h).obj E))
            (adjV.unit.app ((schemeDerivedDirectImage h).obj E)))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction Y (homOfLE inf_le_left)
            adjU adjUV ((schemeDerivedDirectImage h).obj E))
          (-(schemeDerivedOpenDirectImageRestriction Y (homOfLE inf_le_right)
            adjV adjUV ((schemeDerivedDirectImage h).obj E)))) (δ ((schemeDerivedDirectImage
            h).obj E))) ∈ distTriang (schemeDerivedCategory Y) ∧
      (schemeDerivedDirectImage h).mapTriangle.obj (Triangle.mk (biprod.lift (adjU'.unit.app E)
            (adjV'.unit.app E))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left)
            adjU' adjUV' E)
          (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right)
            adjV' adjUV' E))) (δ' E)) ∈
        distTriang (schemeDerivedCategory Y) ∧
      ∃ (cU : (schemeDerivedDirectImage h).obj ((schemeDerivedDirectImage (h ⁻¹ᵁ U).ι).obj
          ((schemeOpenRestriction X (h ⁻¹ᵁ U)).mapDerivedCategory.obj E)) ≅
          (schemeDerivedDirectImage U.ι).obj
          ((schemeOpenRestriction Y U).mapDerivedCategory.obj ((schemeDerivedDirectImage h).obj E)))
        (cV : (schemeDerivedDirectImage h).obj ((schemeDerivedDirectImage (h ⁻¹ᵁ V).ι).obj
          ((schemeOpenRestriction X (h ⁻¹ᵁ V)).mapDerivedCategory.obj E)) ≅
          (schemeDerivedDirectImage V.ι).obj
          ((schemeOpenRestriction Y V).mapDerivedCategory.obj ((schemeDerivedDirectImage h).obj E)))
        (cUV : (schemeDerivedDirectImage h).obj ((schemeDerivedDirectImage ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ
            V)).ι).obj
          ((schemeOpenRestriction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))).mapDerivedCategory.obj E)) ≅
          (schemeDerivedDirectImage (U ⊓ V).ι).obj
          ((schemeOpenRestriction Y (U ⊓ V)).mapDerivedCategory.obj ((schemeDerivedDirectImage
            h).obj E)))
        (e : (schemeDerivedDirectImage h).mapTriangle.obj (Triangle.mk (biprod.lift
            (adjU'.unit.app E) (adjV'.unit.app E))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left)
            adjU' adjUV' E)
          (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right)
            adjV' adjUV' E))) (δ' E)) ≅
          (Triangle.mk (biprod.lift (adjU.unit.app ((schemeDerivedDirectImage h).obj E))
            (adjV.unit.app ((schemeDerivedDirectImage h).obj E)))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction Y (homOfLE inf_le_left)
            adjU adjUV ((schemeDerivedDirectImage h).obj E))
          (-(schemeDerivedOpenDirectImageRestriction Y (homOfLE inf_le_right)
            adjV adjUV ((schemeDerivedDirectImage h).obj E)))) (δ ((schemeDerivedDirectImage
            h).obj E)))),
        cU.hom =
          ((Classical.choice (derivedDirectImageComposition (h ⁻¹ᵁ U).ι h)).symm ≪≫
            eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h U).symm)
              ≪≫ Classical.choice (derivedDirectImageComposition (h ∣_ U) U.ι)).hom.app
                ((schemeOpenRestriction X (h ⁻¹ᵁ U)).mapDerivedCategory.obj E) ≫
          (schemeDerivedDirectImage U.ι).map
            ((Classical.choice (schemeDerivedDirectImage_openRestriction h U)).inv.app E) ∧
        cV.hom =
          ((Classical.choice (derivedDirectImageComposition (h ⁻¹ᵁ V).ι h)).symm ≪≫
            eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h V).symm)
              ≪≫ Classical.choice (derivedDirectImageComposition (h ∣_ V) V.ι)).hom.app
                ((schemeOpenRestriction X (h ⁻¹ᵁ V)).mapDerivedCategory.obj E) ≫
          (schemeDerivedDirectImage V.ι).map
            ((Classical.choice (schemeDerivedDirectImage_openRestriction h V)).inv.app E) ∧
        cUV.hom =
          ((Classical.choice (derivedDirectImageComposition (h ⁻¹ᵁ (U ⊓ V)).ι h)).symm ≪≫
            eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h (U ⊓ V)).symm)
              ≪≫ Classical.choice (derivedDirectImageComposition (h ∣_ (U ⊓ V)) (U ⊓ V).ι)).hom.app
                ((schemeOpenRestriction X (h ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory.obj E) ≫
          (schemeDerivedDirectImage (U ⊓ V).ι).map
            ((Classical.choice (schemeDerivedDirectImage_openRestriction h (U ⊓ V))).inv.app E) ∧
        e.hom.hom₁ = 𝟙 ((schemeDerivedDirectImage h).obj E) ∧
        e.hom.hom₂ = biprod.lift
          ((schemeDerivedDirectImage h).map biprod.fst ≫ cU.hom)
          ((schemeDerivedDirectImage h).map biprod.snd ≫ cV.hom) ∧
        e.hom.hom₃ = cUV.hom := by
  sorry

end AlgebraicGeometry
