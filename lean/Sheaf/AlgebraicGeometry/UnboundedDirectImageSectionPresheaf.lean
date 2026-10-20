/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import Sheaf.AlgebraicGeometry.RingedSpaceDirectImageKInjectiveAcyclic
import Sheaf.AlgebraicGeometry.RingedSpaceSheafificationCohomology

/-!
# Unbounded direct images and the presheaf of local hypercohomology

Source: Stacks Project, Cohomology, Tags 0D5W and 0D5X, with Tag 0BKJ
(blueprint: lem-trf-unbounded-direct-image-section-presheaf).

Right deriving the entire presheaf of sections computes all evaluations on the same
K-injective representative. Exact evaluation and homology give H^q(U,E), and retain
all restrictions. The comparison is the unique map preserving the right-derived units.
The sheafification comparison is normalized on every K-injective representative.
-/

@[expose] public section

set_option autoImplicit false

universe u wX wY

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.RingedSpace

noncomputable section

/-- The ordinary abelian presheaf of sections, with the usual restriction maps.
Source: Stacks, Tags 0D5W and 0D5X
(blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
abbrev localAbelianSections (X : RingedSpace.{u}) :
    ringedSiteModules.{u} (moduleRings X) ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf (moduleRings X) ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

/-- Standard localization of abelian presheaf complexes. This fixes only a size convention.
Source: Stacks, Tag 05RU (blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
instance localAbelianPresheaves_hasDerivedCategory (X : RingedSpace.{u}) :
    HasDerivedCategory ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  HasDerivedCategory.standard _

/-- The published K-injective replacement supplies the arbitrary-quasi-isomorphism
resolution hypothesis of the recorded total right-derived functor.
Source: Stacks, Tag 079P (blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
abbrev localSectionsEnoughKInjectives (X : RingedSpace.{u}) :
    ∀ K : CochainComplex (ringedSiteModules.{u} (moduleRings X)) ℤ,
      ∃ (I : CochainComplex (ringedSiteModules.{u} (moduleRings X)) ℤ) (s : K ⟶ I),
        I.IsKInjective ∧ QuasiIso s :=
  fun K ↦ ⟨(CochainComplex.kInjectiveResolutionFunctor.{u} _).obj K,
    (CochainComplex.toKInjectiveResolution.{u} _).app K, inferInstance,
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ K).2⟩

variable (X : RingedSpace.{u})
  [HasDerivedCategory.{wX} (ringedSiteModules.{u} (moduleRings X))]

/-- Unbounded derived sections on all opens simultaneously. Evaluation at U gives
RGamma(U,-): exact evaluation commutes with the localization, and this right-derived
functor is computed by evaluating the same K-injective representative at U.
Source: Stacks, Tags 0D5W and 0BKJ
(blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
abbrev derivedLocalAbelianSections :
    DerivedCategory (ringedSiteModules.{u} (moduleRings X)) ⥤
      DerivedCategory ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (localAbelianSections X).rightDerivedFunctorOfQuasiIsoResolutions
    (localSectionsEnoughKInjectives X)

/-- V maps to H^q(V,E). Homology in the abelian presheaf category is computed sectionwise;
its functor maps provide restriction and naturality for every derived morphism.
Source: Stacks, Tags 0D5W and 0D5X
(blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
abbrev localHypercohomologyPresheaf (q : ℤ) :
    DerivedCategory (ringedSiteModules.{u} (moduleRings X)) ⥤
      (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  derivedLocalAbelianSections X ⋙ DerivedCategory.homologyFunctor _ q

variable {X}
variable {Y : RingedSpace.{u}}
  [HasDerivedCategory.{wY} (ringedSiteModules.{u} (moduleRings Y))]

/-- Rf_* using the recorded universal-pair construction on K-injective representatives.
The ordinary direct image is the published moduleDirectImage, including f-sharp.
Source: Stacks, Tag 079V (blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
abbrev sectionDerivedDirectImage (f : X ⟶ Y) :
    DerivedCategory (ringedSiteModules.{u} (moduleRings X)) ⥤
      DerivedCategory (ringedSiteModules.{u} (moduleRings Y)) :=
  (moduleDirectImage f).rightDerivedFunctorOfQuasiIsoResolutions
    (localSectionsEnoughKInjectives X)

/-- The presheaf V maps to H^q(f^-1 V,E): right derive the actual inverse-image section
functor, whose underlying abelian groups and restrictions are literally F(f^-1 V).
Source: Stacks, Tag 0D5X (blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
abbrev inverseOpenHypercohomologyPresheaf (f : X ⟶ Y) (q : ℤ) :
    DerivedCategory (ringedSiteModules.{u} (moduleRings X)) ⥤
      (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (moduleDirectImage f ⋙ localAbelianSections Y).rightDerivedFunctorOfQuasiIsoResolutions
      (localSectionsEnoughKInjectives X) ⋙ DerivedCategory.homologyFunctor _ q

/-- The composite right-derived unit for f_* followed by sections. No assertion that f_*
preserves K-injectivity is used: for general ringed spaces the needed fact is acyclicity.
Source: Stacks, Tag 0D5W (blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
def localLerayCompositeUnit (f : X ⟶ Y) :
    (moduleDirectImage f ⋙ localAbelianSections Y).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (sectionDerivedDirectImage f ⋙ derivedLocalAbelianSections Y) :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (moduleDirectImage f ⋙ localAbelianSections Y)) (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ))
      ((localAbelianSections Y).rightDerivedFunctorOfQuasiIsoResolutionsUnit
        (localSectionsEnoughKInjectives Y)) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      ((moduleDirectImage f).rightDerivedFunctorOfQuasiIsoResolutionsUnit
        (localSectionsEnoughKInjectives X)) (derivedLocalAbelianSections Y) ≫
    (Functor.associator _ _ _).hom

/-- The unique canonical Leray comparison obtained from the universal bijection of the
recorded total right-derived functor. The choice is uniquely determined by its unit.
Source: Stacks, Tag 0D5W (blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
def localLerayComparison (f : X ⟶ Y) :
    (moduleDirectImage f ⋙ localAbelianSections Y).rightDerivedFunctorOfQuasiIsoResolutions
        (localSectionsEnoughKInjectives X) ⟶
      sectionDerivedDirectImage f ⋙ derivedLocalAbelianSections Y :=
  Classical.choose
    ((Functor.rightDerivedFunctorOfQuasiIsoResolutions_universal
      (moduleDirectImage f ⋙ localAbelianSections Y) (localSectionsEnoughKInjectives X)
        (sectionDerivedDirectImage f ⋙ derivedLocalAbelianSections Y)).surjective
      (localLerayCompositeUnit f))

/-- The canonical comparison on the two abelian presheaves, natural in the derived input.
Source: Stacks, Tags 0D5W and 0D5X
(blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
def localHypercohomologyComparison (f : X ⟶ Y) (q : ℤ) :
    inverseOpenHypercohomologyPresheaf f q ⟶
      sectionDerivedDirectImage f ⋙ localHypercohomologyPresheaf Y q :=
  Functor.whiskerRight (localLerayComparison f) (DerivedCategory.homologyFunctor _ q)

/-- The fixed, canonical sheafification comparison on a complex. Exact sheafification
commutes with homology, its counit recovers a sheaf, and forgetting modules is exact.
Source: Stacks, Tag 0BKJ (blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
def localSectionComplexSheafificationIso (Y : RingedSpace.{u}) (q : ℤ)
    (I : CochainComplex (ringedSiteModules.{u} (moduleRings Y)) ℤ) :
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        ((((localAbelianSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology q) ≅
      (SheafOfModules.toSheaf (moduleRings Y)).obj (I.homology q) :=
  let T := SheafOfModules.toSheaf (moduleRings Y)
  let U := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  let S := presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
  let e : (T ⋙ U) ⋙ S ≅ T :=
    Functor.associator T U S ≪≫
      Functor.isoWhiskerLeft T (asIso (sheafificationAdjunction _ _).counit) ≪≫
        T.rightUnitor
  (Functor.isoWhiskerLeft ((T ⋙ U).mapHomologicalComplex (ComplexShape.up ℤ))
      (S.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) q).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q) ≪≫
    T.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) q).app I

/-- Normalization of the sheafification isomorphism on any K-injective representative.
The three factors are the right-derived unit, ordinary exact sheafification, and the
localization's homology comparison. Thus this specifies an isomorphism uniquely.
Source: Stacks, Tags 0BKJ and 0D5X
(blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
def localHypercohomologySheafificationModel (q : ℤ)
    (I : CochainComplex (ringedSiteModules.{u} (moduleRings Y)) ℤ) [I.IsKInjective] :
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        ((localHypercohomologyPresheaf Y q).obj (DerivedCategory.Q.obj I)) ≅
      (SheafOfModules.toSheaf (moduleRings Y)).obj
        ((DerivedCategory.homologyFunctor _ q).obj (DerivedCategory.Q.obj I)) :=
  (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).mapIso
      ((DerivedCategory.homologyFunctor _ q).mapIso
          ((localAbelianSections Y).rightDerivedFunctorOfQuasiIsoResolutionsObjIso
            (localSectionsEnoughKInjectives Y) (𝟙 I)) ≪≫
        (DerivedCategory.homologyFunctorFactors _ q).app
          (((localAbelianSections Y).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≪≫
    localSectionComplexSheafificationIso Y q I ≪≫
    (SheafOfModules.toSheaf (moduleRings Y)).mapIso
      ((DerivedCategory.homologyFunctorFactors _ q).app I).symm

/-- The same normalized sheafification comparison at any derived object. A chosen complex
representative and its published K-injective replacement merely compute the canonical map;
the natural isomorphism below is required to agree with these components.
Source: Stacks, Tag 0BKJ (blueprint: lem-trf-unbounded-direct-image-section-presheaf). -/
def localHypercohomologySheafificationAt (q : ℤ)
    (M : DerivedCategory (ringedSiteModules.{u} (moduleRings Y))) :
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        ((localHypercohomologyPresheaf Y q).obj M) ≅
      (SheafOfModules.toSheaf (moduleRings Y)).obj
        ((DerivedCategory.homologyFunctor _ q).obj M) :=
  let K := DerivedCategory.Q.objPreimage M
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u} _).obj K
  let s := (CochainComplex.toKInjectiveResolution.{u} _).app K
  letI : QuasiIso s :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ K).2
  let a : DerivedCategory.Q.obj I ≅ M :=
    (asIso (DerivedCategory.Q.map s)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso M
  (localHypercohomologyPresheaf Y q ⋙
      presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).mapIso a.symm ≪≫
    localHypercohomologySheafificationModel q I ≪≫
    (DerivedCategory.homologyFunctor _ q ⋙ SheafOfModules.toSheaf (moduleRings Y)).mapIso a

/-- The local Leray comparison is an isomorphism of abelian presheaves in every integer
 degree, and sheafification is canonically the underlying abelian cohomology sheaf.
Both comparisons are natural in E; presheaf morphisms include all restriction squares.
The specified map and displayed K-injective normalization exclude arbitrary isomorphisms.
Source: Stacks, Tags 0D5W, 0D5X and 0BKJ
(blueprint: lem-trf-unbounded-direct-image-section-presheaf).

Proof plan:
1. Represent E by a complex C and choose its functorial K-injective replacement I_X(C).
   Put B=f_*I_X(C) and resolve it on Y by r:B -> J. These are exactly the representatives
   of the recorded universal right-derived functors and their units.
2. For V in Y put U=f^-1 V. Restriction to an open is exact and preserves K-injectives
   (lem-sc-derived-open-restriction-adjunction-exact,
   lem-sc-derived-k-injective-restrict-open). Thus J|V resolves B|V=(f|U)_*(I|U).
3. Apply lem-pc-ringed-space-direct-image-kinjective-acyclic to f|U followed by the
   map from V to the one-point ringed space with ring O_Y(V). Its direct image is
   sections over V. The right-derived unit on B|V is invertible. Naturality with r|V
   shows that sections of r induce an isomorphism in every cohomological degree.
4. Those maps are the single natural comparison of the universal units defined above.
   They commute with restrictions and chain maps. Quasi-isomorphisms between K-injectives
   are homotopy equivalences (lem-weil-pbc-kinjective-hom-derived), so the comparison
   descends to all derived morphisms and is independent of the representative.
5. Exact sheafification of sectionwise cohomology gives the cohomology sheaf (Tag 0BKJ,
   lem-pc-ringed-space-sheafification-cohomology), with precisely the model above.
   Every derived object has a K-injective representative, so this normalization gives
   existence of the normalized natural isomorphism. Whisker by Rf_* and compose
   with the sheafified presheaf comparison to obtain the assertion for either presheaf.
No bound, scheme assumption or finiteness property is used. -/
theorem unboundedDirectImage_sectionPresheaf (f : X ⟶ Y) (q : ℤ) :
    ∃ e : inverseOpenHypercohomologyPresheaf f q ≅
        sectionDerivedDirectImage f ⋙ localHypercohomologyPresheaf Y q,
      e.hom = localHypercohomologyComparison f q ∧
        ∃ s : (sectionDerivedDirectImage f ⋙ localHypercohomologyPresheaf Y q) ⋙
            presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ≅
          sectionDerivedDirectImage f ⋙
            (DerivedCategory.homologyFunctor (ringedSiteModules.{u} (moduleRings Y)) q ⋙
              SheafOfModules.toSheaf (moduleRings Y)),
          (∀ E : DerivedCategory (ringedSiteModules.{u} (moduleRings X)),
            s.app E = localHypercohomologySheafificationAt q
              ((sectionDerivedDirectImage f).obj E)) ∧
          ∃ t : inverseOpenHypercohomologyPresheaf f q ⋙
              presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ≅
            sectionDerivedDirectImage f ⋙
              (DerivedCategory.homologyFunctor (ringedSiteModules.{u} (moduleRings Y)) q ⋙
                SheafOfModules.toSheaf (moduleRings Y)),
            t = Functor.isoWhiskerRight e
              (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) ≪≫ s := by
  sorry

end

end AlgebraicGeometry.RingedSpace
