/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.SecondLocalizationMap
/-! # Naturality for second localization
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-second-localization-naturality). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace RingTensorCohomology

variable (R A B Bp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Bp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra B Bp] [Algebra R Bp]
  [tRB : IsScalarTower R B Bp]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[R] Bp) D]
  [Algebra A D] [Algebra B D] [Algebra Bp D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tApD : IsScalarTower A (A ⊗[R] Bp) D]
  [tBpD : IsScalarTower Bp (A ⊗[R] Bp) D]
  [tBBpD : IsScalarTower B Bp D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

include tRB tAD tBD tApD tBpD tBBpD in
/-- Naturality of the characterized coefficient map on arbitrary models.
Source: Stacks Project, Tag 06Y6; Tag 0DJ8.
(blueprint: lem-pc-second-localization-naturality).

Proof: leftDerived_ext applied to the target model K' proves that the derived
lift for L followed by epsilon equals delta extended to Bp followed by the
lift for L'. Their composites with K'.counit agree by the two given counit
compatibilities and naturality of the ordinary associator. Naturality of each
derived lift with respect to the image of f gives the full commuting derived
square. Apply homology and naturality of flatDerivedHomologyIso, then conjugate
by cohomologyIso. The characterizations of g and h give equality of the
underlying B-linear maps. On a generator 1 tensor x the two formulas he and he'
and ExtendScalars.map_tmul identify the D-linear composites with this equality.
ExtendScalars.hom_ext proves equality of the maps. This works for arbitrary
flat B to Bp and uses no localization or flatness of D. Zero maps, identity
maps and zero rings obey the same equations. -/
theorem secondLocalization_naturality (hflat : (algebraMap B Bp).Flat) (i : ℤ)
    (Q Q' : CochainComplex (ModuleCat.{u} A) ℤ) (f : Q ⟶ Q')
          (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
          (K : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D)
          (L' : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q' D)
          (K' : ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q' D)
          (δ : L.derived ⟶ L'.derived) (ε : K.derived ⟶ K'.derived)
          (g : L.cohomology i ⟶ L'.cohomology i)
          (h : K.cohomology i ⟶ K'.cohomology i)
    (e : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ≅
      (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).obj (K.cohomology i))
    (e' : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L'.cohomology i) ≅
      (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).obj (K'.cohomology i))
    (he : IsSecondLocalizationMap R A B Bp D hflat Q L K i e.hom)
    (he' : IsSecondLocalizationMap R A B Bp D hflat Q' L' K' i e'.hom) :
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) δ ≫
            L'.counit = L.counit →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g ≫
              (L'.cohomologyIso i).hom =
          (L.cohomologyIso i).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (L.derived.map (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                  ((restrict R A).map f)))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (δ.app (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                  ((restrict R A).obj Q')))) →
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) ε ≫
            K'.counit = K.counit →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : Bp →ₐ[R] A ⊗[R] Bp).toRingHom).map h ≫
              (K'.cohomologyIso i).hom =
          (K.cohomologyIso i).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i).map
              (K.derived.map (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                  ((restrict R A).map f)))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i).map
              (ε.app (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                  ((restrict R A).obj Q')))) →
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map g ≫
            e'.hom =
          e.hom ≫
            (ModuleCat.extendScalars (algebraMap (A ⊗[R] Bp) D)).map h := by
  sorry

end RingTensorCohomology
