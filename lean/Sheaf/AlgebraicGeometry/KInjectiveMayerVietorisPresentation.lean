/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisExact
import Sheaf.AlgebraicGeometry.KInjectiveMayerVietorisComparisons

/-! # The short exact complex presenting direct-image Mayer--Vietoris

Source: Stacks Project, Cohomology, Tag 08BV, proof before passage to the triangle.
(blueprint: lem-pc-kinjective-mayer-vietoris-presentation).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- The transported restriction functors require extra elaboration heartbeats.
/-- The injective representative gives a short exact sequence with comparisons of
its first two arrows to the derived units and the difference of restriction maps.
Source: Stacks Project, Cohomology, Tag 08BV, construction of the short exact sequence
and its identification with the three derived direct-image objects.
(blueprint: lem-pc-kinjective-mayer-vietoris-presentation).

Proof:
For each open W among U, V and their intersection, restrict I termwise. Exact
extension by zero is left adjoint to restriction, so restriction preserves
K-injectivity (Tag 08BS). Transport from the localized module site to the open
subscheme using Scheme.Modules.overEquiv. Put J_W = j_W* (I|W), with the
underived module direct image applied termwise. Set B = J_U biproduct J_V and
C = J_(U intersection V). Define f as the pair of restriction units and g as
the difference of the two restrictions to the intersection. Naturality of the
sheaf restrictions makes these chain maps, and the two iterated restrictions
agree, so f followed by g is zero. On each test open T and in degree n, the
sequence is I^n(T) -> I^n(T intersection U) plus I^n(T intersection V) ->
I^n(T intersection U intersection V). Since U and V cover X, uniqueness and
existence of sheaf gluing give a zero kernel and the equalizer at the middle.
Injectivity of I^n makes restriction to a smaller open surjective (Tag 01EA):
lift any intersection section to T intersection U and take zero in the other
summand. Thus the sequence is short exact on sections, hence short exact as
sheaves and degreewise as complexes.
Derive the restriction/direct-image adjunction, using exactness of restriction
and K-injective resolutions for its right adjoint. Its unit on a K-injective
representative is the localized underived restriction unit. The right-derived
unit on the restricted K-injective complexes identifies Q(J_W) with Rj_W*(E|W),
after composing with the exact-restriction comparison and e. The biproduct
comparison for Q gives eB; the intersection comparison gives eC. Naturality
of e identifies Q(f) with the pair of derived units. For Q(g), transpose each
restriction along the derived adjunction: its transpose is the restriction of
the U or V counit, conjugated by the canonical nested-restriction comparison.
This is exactly schemeDerivedOpenDirectImageRestriction. Additivity and the
biproduct comparison identify the second arrow with their difference.
For arbitrary given adjunctions, compare each with the derived restriction
adjunction by uniqueness of right adjoints. This gives an automorphism of each
right-adjoint functor, carrying the canonical unit to the supplied unit. Compose
each object comparison with that automorphism. Naturality and the unit/counit
identities show that the adjoint restriction maps are conjugated by the same
automorphisms, giving the two displayed identities for the supplied adjunctions.
No connecting morphism or distinguished-triangle assertion is included here.
The construction also works for empty opens or repeated opens. -/
theorem schemeKInjective_mayerVietoris_presentation
    (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] (hI : ∀ n : ℤ, Injective (I.X n))
    (E : schemeDerivedCategory X) (e : DerivedCategory.Q.obj I ≅ E)
    (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
    (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
    (adjUV : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣
      schemeDerivedDirectImage (U ⊓ V).ι) :
    ∃ (B C : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (f : I ⟶ B) (g : B ⟶ C) (hz : f ≫ g = 0)
      (eB : DerivedCategory.Q.obj B ≅
        (schemeDerivedDirectImage U.ι).obj
          ((schemeOpenRestriction X U).mapDerivedCategory.obj E) ⊞
        (schemeDerivedDirectImage V.ι).obj
          ((schemeOpenRestriction X V).mapDerivedCategory.obj E))
      (eC : DerivedCategory.Q.obj C ≅
        (schemeDerivedDirectImage (U ⊓ V).ι).obj
          ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj E)),
      (ShortComplex.mk f g hz).ShortExact ∧
      DerivedCategory.Q.map f ≫ eB.hom =
        e.hom ≫ biprod.lift (adjU.unit.app E) (adjV.unit.app E) ∧
      DerivedCategory.Q.map g ≫ eC.hom = eB.hom ≫
        biprod.desc
          (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left) adjU adjUV E)
          (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right) adjV adjUV E)) := by
  obtain ⟨eU, eV, eW, hu, hv, hru, hrv⟩ :=
    schemeOpenModuleImageComplex_comparisons X U V I E e adjU adjV adjUV
  let Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ⥤
      schemeDerivedCategory X := DerivedCategory.Q
  have : PreservesBinaryBiproducts Q :=
    preservesBinaryBiproducts_of_preservesBiproducts Q
  let eB : DerivedCategory.Q.obj (schemeMayerVietorisB X U V I) ≅
      (schemeDerivedDirectImage U.ι).obj
        ((schemeOpenRestriction X U).mapDerivedCategory.obj E) ⊞
      (schemeDerivedDirectImage V.ι).obj
        ((schemeOpenRestriction X V).mapDerivedCategory.obj E) :=
    Q.mapBiprod (schemeOpenModuleImageComplex X U I)
      (schemeOpenModuleImageComplex X V I) ≪≫ biprod.mapIso eU eV
  refine ⟨schemeMayerVietorisB X U V I, schemeOpenModuleImageComplex X (U ⊓ V) I,
    schemeMayerVietorisF X U V I, schemeMayerVietorisG X U V I,
    schemeMayerVietoris_zero X U V I, eB, eW,
    schemeMayerVietorisComplex_shortExact X U V hcover I hI, ?_, ?_⟩
  · dsimp only [schemeMayerVietorisF, eB, Iso.trans_hom, biprod.mapIso]
    rw [← Category.assoc, biprod.map_lift_mapBiprod]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst]
      rw [← Category.assoc, biprod.lift_fst]
      simpa [Category.assoc] using hu
    · simp only [Category.assoc, biprod.map_snd]
      rw [← Category.assoc, biprod.lift_snd]
      simpa [Category.assoc] using hv
  · dsimp only [schemeMayerVietorisG, eB, Iso.trans_hom, biprod.mapIso]
    rw [← biprod.mapBiprod_hom_desc Q]
    simp only [Category.assoc]
    apply congrArg (fun k => (Q.mapBiprod
      (schemeOpenModuleImageComplex X U I) (schemeOpenModuleImageComplex X V I)).hom ≫ k)
    apply biprod.hom_ext'
    · simpa [Category.assoc] using hru
    · simpa [Category.assoc] using congrArg Neg.neg hrv

end AlgebraicGeometry
