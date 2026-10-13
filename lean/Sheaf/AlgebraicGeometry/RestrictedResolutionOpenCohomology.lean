/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices

/-! # Restriction on the homology of fixed-resolution section complexes

Source: Stacks Project, Tags 01E4 and 01FB.
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

/-- Restriction between arbitrary opens on the homology of a fixed resolution's
section complexes, before the map to a cohomology sheaf.
Source: Stacks Project, Equation 20.7.1.1 (Tag 01E2), Remark 20.14.2 (Tag 01FB).
(blueprint: new-restricted-resolution-open-cohomology)

Proof: Put j = homOfLE e. Form the complex isomorphism t from j^*R.resolution
to R'.resolution by j^*(R.comparison), the canonical isomorphism j^*(I|U) = I|L,
and R'.comparison inverse, in that order. Let beta be the restriction unit on
R.resolution followed by j_*(t). Naturality of the unit and the two augmentation
equations show that beta lifts the coefficient map displayed below.
Restriction preserves finite limits, so pushforward along j preserves injectives.
Use this pushed resolution itself as the injective comparison complex in
ModuleCohomologyFMapData, with lambda the identity. The canonical global section
comparison is an isomorphism (the inverse image of the top open is top).
Independence of that data computes the displayed cohomology map by this lift.
Cancel the two resolution isomorphisms and apply homology to the surviving
section-complex map. The pinned components of R.sections and R'.sections and
the restriction-composition identity identify it, termwise, with restriction of
I's sections from U to L. The augmentation equations supply the degree-zero
compatibility of the lift. All constructions apply to empty or equal opens,
the zero coefficient, and degree zero; no restriction is inverted. -/
theorem restrictedResolution_open_cohomology {Z : Scheme.{u}} {F : Z.Modules}
    (I : InjectiveResolution F) (U L : Z.Opens) (e : L ≤ U)
    (R : RestrictedResolutionSections I U) (R' : RestrictedResolutionSections I L)
    (p : ℕ) :
    let := RingedSpace.globalSectionsFunctor_additive Z.toRingedSpace
    let := RingedSpace.globalSectionsFunctor_additive U.toScheme.toRingedSpace
    let := RingedSpace.globalSectionsFunctor_additive L.toScheme.toRingedSpace
    let j := Z.homOfLE e
    let c := (restrictFunctorComp j U.ι).symm.app F ≪≫
      (restrictFunctorCongr (Z.homOfLE_ι e)).app F
    moduleCohomologyFMap j
      ((restrictAdjunction j).unit.app ((restrictFunctor U.ι).obj F) ≫
        (pushforward j).map c.hom) p ≫
      (forget₂ _ AddCommGrpCat.{u}).map
        (R'.resolution.isoRightDerivedObj
          (RingedSpace.globalSectionsFunctor L.toScheme.toRingedSpace) p).hom ≫
      (((RingedSpace.globalSectionsComplex R'.resolution).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{u})).inv ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
        R'.sections.hom =
    (forget₂ _ AddCommGrpCat.{u}).map
      (R.resolution.isoRightDerivedObj
        (RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace) p).hom ≫
      (((RingedSpace.globalSectionsComplex R.resolution).sc p).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{u})).inv ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
      R.sections.hom ≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
        ((NatTrans.mapHomologicalComplex
          (Functor.whiskerLeft (SheafOfModules.forget Z.ringCatSheaf ⋙
            PresheafOfModules.toPresheaf Z.ringCatSheaf.obj)
              ((evaluation Z.Opensᵒᵖ AddCommGrpCat.{u}).map
                (homOfLE e).op))
          (ComplexShape.up ℕ)).app I.cocomplex) := by sorry

end AlgebraicGeometry.Scheme.Modules
