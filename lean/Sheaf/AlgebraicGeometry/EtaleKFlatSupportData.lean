/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.EtaleInjectiveSupportSequence
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-!
# Canonical data for the K-flat ordinary etale support diagram

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Locality, expanded by the agent-written
support diagram; Stacks Tags 03DB, 03ER, 06YU, 07A4, 0FPI, 0152 and 014A
(blueprint: def-pur-etale-kflat-support-data).

The main constructions are `IsRightMap`, `totalTensorSequence`, `tensorModel`,
`sourceThirdModel`, `replacementIso`, `targetThirdModel` and `restrictedProjection`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] HomologicalComplex.monoidalCategoryStruct
universe u uC vC uD vD w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.KFlatSupportComparison

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.leftAdjoint Functor.rightAdjoint Functor.leftDerivedFunctor
  upperStar lowerStar closedUpperShriek ProEtale.pbcFixedScalarExtension
  _root_.DerivedCategory.Q _root_.DerivedCategory.Qh


/-- Abbreviation for the existing category of ordinary etale cochain module sheaves.
Source: Stacks 03DA, 06YU (blueprint: def-pur-etale-kflat-support-data). -/
abbrev Complex (A : Type (u + 1)) [CommRing A] (P : Scheme.{u}) :=
  CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ

/-- The existing localization functor, with its ordinary etale coefficient category explicit.
Source: Stacks 05RU (blueprint: def-pur-etale-kflat-support-data). -/
abbrev localize (A : Type (u + 1)) [CommRing A] (P : Scheme.{u}) :
    Complex A P ⥤ DerivedCategoryModule A P :=
  _root_.DerivedCategory.Q (C := Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A))

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
  {Z P U : Scheme.{u}}

/-- The existing exact ordinary open inverse image on complexes, with both categories explicit.
Source: Stacks 07A4 (blueprint: def-pur-etale-kflat-support-data). -/
abbrev pullComplex (A : Type (u + 1)) [CommRing A] (j : U ⟶ P) :
    Complex A P ⥤ Complex A U :=
  (upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)

/-- The existing ordinary open direct image on complexes, with both categories explicit.
Source: Stacks 07A4 (blueprint: def-pur-etale-kflat-support-data). -/
abbrev pushComplex (A : Type (u + 1)) [CommRing A] (j : U ⟶ P) :
    Complex A U ⥤ Complex A P :=
  (lowerStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)

/-- The exact-pullback version of the existing normalized scalar/pullback isomorphism.
Source: Stacks 07A4 (blueprint: def-pur-etale-kflat-support-data). -/
def scalarOpenIso (φ : A →+* B) (j : U ⟶ P) :
    scalarExtension φ P ⋙ D(upperStar (ModuleCat.{u + 1} B) j) ≅
      D(upperStar (ModuleCat.{u + 1} A) j) ⋙ scalarExtension φ U :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).symm ≪≫
    scalarPullbackIso φ j ≪≫ Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j) _

/-- The exact-pullback version of the existing inverse-image/scalar-restriction comparison.
Source: Stacks 0D6J, 07A4 (blueprint: def-pur-etale-kflat-support-data). -/
def restrictionOpenIso (φ : A →+* B) (j : U ⟶ P) :
    Sheaf.derivedRestrictScalars P.smallEtaleTopology φ ⋙
        D(upperStar (ModuleCat.{u + 1} A) j) ≅
      D(upperStar (ModuleCat.{u + 1} B) j) ⋙
        Sheaf.derivedRestrictScalars U.smallEtaleTopology φ :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm ≪≫
    scalarRestrictionPullbackIso φ j ≪≫ Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j) _


/-- Adjunct formula in any monoidal adjunction. The two tensor maps are the canonical
oplax/lax comparison of the strong monoidal left adjoint.
Source: Stacks 07A4 (blueprint: def-pur-etale-kflat-support-data). -/
def tensorAdjunct {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Monoidal] (adj : F ⊣ G)
    (Q I J : C) (a : Q ⊗ I ⟶ J) : Q ⊗ G.obj (F.obj I) ⟶ G.obj (F.obj J) :=
  adj.homEquiv _ _
    (Functor.OplaxMonoidal.δ F Q (G.obj (F.obj I)) ≫
      F.obj Q ◁ adj.counit.app (F.obj I) ≫
      Functor.LaxMonoidal.μ F Q I ≫ F.map a)

/-- Summand characterization of the total adjunct, including every total degree.
Source: Stacks 07A4, 0FPI (blueprint: def-pur-etale-kflat-support-data). -/
def IsTotalAdjunct {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Preadditive D] [HasZeroObject D] [MonoidalCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] [F.Monoidal]
    (adj : F ⊣ G) (Q I J : CochainComplex C ℤ) (a : Q ⊗ I ⟶ J)
    (v : Q ⊗ ((G.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj I)) ⟶
      (G.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj J)) :
    Prop :=
  ∀ (p q n : ℤ) (h : p + q = n),
    HomologicalComplex.ιTensorObj Q ((G.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj I)) p q n h ≫ v.f n =
      tensorAdjunct adj (Q.X p) (I.X q) (J.X n)
        (HomologicalComplex.ιTensorObj Q I p q n h ≫ a.f n)

/-- The étale specialization of the canonical total-summand characterization.
Source: Stacks 07A4, 0FPI (blueprint: def-pur-etale-kflat-support-data). -/
def IsRightMap {A : Type (u + 1)} [CommRing A] {P U : Scheme.{u}}
    (j : U ⟶ P) (Q I J : Complex A P) (a : Q ⊗ I ⟶ J)
    (v : Q ⊗ ((pushComplex A j).obj ((pullComplex A j).obj I)) ⟶
      (pushComplex A j).obj ((pullComplex A j).obj J)) : Prop :=
  IsTotalAdjunct (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j) Q I J a v

/-- The existing one-sided K-flat comparison followed by the augmentation and a
representing isomorphism, with the existing signed cochain interchange.
Source: Stacks 06YU (blueprint: def-pur-etale-kflat-support-data). -/
def tensorModelOfAugmentation {C : Type uC} [Category.{vC} C] [Abelian C]
    [IsGrothendieckAbelian.{vC} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [HasDerivedCategory.{vC} C]
    [Abelian.HasFunctorialFlatResolution C]
    (Q : CochainComplex C ℤ) (hQ : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q)
    (B : C) (π : Q ⟶ (CochainComplex.singleFunctor C 0).obj B) [QuasiIso π]
    (I : CochainComplex C ℤ) (L : _root_.DerivedCategory C)
    (e : _root_.DerivedCategory.Q.obj I ≅ L) :
    _root_.DerivedCategory.Q.obj (Q ⊗ I) ≅
      L ⊗ (_root_.DerivedCategory.singleFunctor C 0).obj B :=
  _root_.DerivedCategory.Q.mapIso (β_ Q I) ≪≫
    (_root_.DerivedCategory.QObjTensorQObjIsoOfKFlatRight (C := C) I Q hQ).symm ≪≫
    tensorIso (C := _root_.DerivedCategory C) e (asIso (_root_.DerivedCategory.Q.map π) ≪≫
      (_root_.DerivedCategory.singleFunctorIsoCompQ C 0).symm.app B)

/-- Canonical tensor-model identification, including signed interchange putting B second.
The resolution and all its terms have only an A-action.
Source: Stacks 06YU, 0GL6 (blueprint: def-pur-etale-kflat-support-data). -/
def tensorModel (φ : A →+* B) (Q : Complex A P)
    (π : Q ⟶ (CochainComplex.singleFunctor
      (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj (scalarCoefficientSheaf φ P))
    [QuasiIso π] (hQ : (HomologicalComplex.quasiIso
      (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)).kFlat Q)
    (I : Complex A P) (L : DerivedCategoryModule A P)
    (e : (localize A P).obj I ≅ L) :
    (localize A P).obj (Q ⊗ I) ≅
      (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).obj
        ((scalarExtension φ P).obj L) :=
  tensorModelOfAugmentation
    (C := Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A))
      Q hQ (scalarCoefficientSheaf φ P) π I L e ≪≫
    ((eqToIso (scalarTensorFunctor_eq φ P)).symm.app L) ≪≫
    (scalarTensorIso φ P).symm.app L

/-- The canonical B-linear coefficient projection, with exact open inverse image.
Source: Stacks 0GL6 (blueprint: def-pur-etale-kflat-support-data). -/
def coefficientProjection (φ : A →+* B) (j : U ⟶ P) (L : DerivedCategoryModule A P) :
    (scalarExtension φ P).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
          ((D(upperStar (ModuleCat.{u + 1} A) j)).obj L)) ⟶
      (R(lowerStar (ModuleCat.{u + 1} B) j)).obj
        ((D(upperStar (ModuleCat.{u + 1} B) j)).obj ((scalarExtension φ P).obj L)) :=
  (scalarMate φ j).app ((D(upperStar (ModuleCat.{u + 1} A) j)).obj L) ≫
    (R(lowerStar (ModuleCat.{u + 1} B) j)).map ((scalarOpenIso φ j).inv.app L)

/-- Restriction of the coefficient projection followed by the canonical direct-image
and inverse-image restriction comparisons. On the bounded-below objects in the theorem
these comparisons are isomorphisms; their actual counit-normalized maps are used here.
Source: Stacks 0GL6, 0D6J (blueprint: def-pur-etale-kflat-support-data). -/
def restrictedProjection (φ : A →+* B) (j : U ⟶ P) (L : DerivedCategoryModule A P) :
    (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).obj
        ((scalarExtension φ P).obj
          ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
            ((D(upperStar (ModuleCat.{u + 1} A) j)).obj L))) ⟶
      (R(lowerStar (ModuleCat.{u + 1} A) j)).obj
        ((D(upperStar (ModuleCat.{u + 1} A) j)).obj
          ((Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).obj
            ((scalarExtension φ P).obj L))) :=
  (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).map
      (coefficientProjection φ j L) ≫
    (scalarRestrictionDirectImageMap φ j).app
      ((D(upperStar (ModuleCat.{u + 1} B) j)).obj ((scalarExtension φ P).obj L)) ≫
    (R(lowerStar (ModuleCat.{u + 1} A) j)).map
      ((restrictionOpenIso φ j).inv.app ((scalarExtension φ P).obj L))

/-- Apply the existing total-tensor functor to a short complex of complexes.
Source: Stacks 012Z, 06YU (blueprint: def-pur-etale-kflat-support-data). -/
abbrev totalTensorSequence {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C]
    (Q : CochainComplex C ℤ) (S : ShortComplex (CochainComplex C ℤ)) :
    ShortComplex (CochainComplex C ℤ) :=
  S.map (tensorLeft Q)

/-- Functoriality of the same total-tensor short-complex construction.
Source: Stacks 012Z, 06YU (blueprint: def-pur-etale-kflat-support-data). -/
def totalTensorSequenceMap {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasColimitsOfSize.{0, 0} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C]
    (Q : CochainComplex C ℤ) {S S' : ShortComplex (CochainComplex C ℤ)} (f : S ⟶ S') :
    totalTensorSequence Q S ⟶ totalTensorSequence Q S' :=
  (tensorLeft Q).mapShortComplex.map f

/-- The canonical identification on the top quotient term uses the support-sequence
computation of Rj_*j^*L before the coefficient tensor identification.
Source: Stacks 06YU, 093X (blueprint: def-pur-etale-kflat-support-data). -/
def sourceThirdModel (φ : A →+* B) (j : U ⟶ P) [IsOpenImmersion j]
    (Q : Complex A P)
    (π : Q ⟶ (CochainComplex.singleFunctor
      (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj (scalarCoefficientSheaf φ P))
    [QuasiIso π] (hQ : (HomologicalComplex.quasiIso
      (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)).kFlat Q)
    (I : Complex A P) (L : DerivedCategoryModule A P)
    (e : (localize A P).obj I ≅ L)
    (hI : CochainComplex.IsKInjective
      ((pullComplex A j).obj I)) :
    (localize A P).obj
        (Q ⊗ ((pullComplex A j ⋙
          pushComplex A j).obj I)) ≅
      (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).obj
        ((scalarExtension φ P).obj
          ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
            ((D(upperStar (ModuleCat.{u + 1} A) j)).obj L))) :=
  tensorModel φ Q π hQ ((pushComplex A j).obj ((pullComplex A j).obj I))
    ((R(lowerStar (ModuleCat.{u + 1} A) j)).obj
      ((D(upperStar (ModuleCat.{u + 1} A) j)).obj L))
    (etaleSupportThirdComparison A j I hI ≪≫
    (R(lowerStar (ModuleCat.{u + 1} A) j)).mapIso
      ((D(upperStar (ModuleCat.{u + 1} A) j)).mapIso e))

/-- Transport a representing isomorphism across the actual localized quasi-isomorphism.
Source: Stacks 05RU, 079P (blueprint: def-pur-etale-kflat-support-data). -/
def replacementIso {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasDerivedCategory.{w} C] {N J : CochainComplex C ℤ}
    (a : N ⟶ J) [QuasiIso a] {L : _root_.DerivedCategory C}
    (eN : _root_.DerivedCategory.Q.obj N ≅ L) : _root_.DerivedCategory.Q.obj J ≅ L :=
  (asIso (_root_.DerivedCategory.Q.map a)).symm ≪≫ eN

/-- The target quotient identification is the support-sequence comparison at J,
followed by the specified identification of its represented object.
Source: Stacks 093X, 0GL6 (blueprint: def-pur-etale-kflat-support-data). -/
def targetThirdModel (φ : A →+* B) (j : U ⟶ P) [IsOpenImmersion j]
    (J : Complex A P) (L : DerivedCategoryModule A P)
    (e : (localize A P).obj J ≅
      (Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).obj
        ((scalarExtension φ P).obj L))
    (hJ : CochainComplex.IsKInjective
      ((pullComplex A j).obj J)) :
    (localize A P).obj
        ((pullComplex A j ⋙
          pushComplex A j).obj J) ≅
      (R(lowerStar (ModuleCat.{u + 1} A) j)).obj
        ((D(upperStar (ModuleCat.{u + 1} A) j)).obj
          ((Sheaf.derivedRestrictScalars P.smallEtaleTopology φ).obj
            ((scalarExtension φ P).obj L))) :=
  etaleSupportThirdComparison A j J hJ ≪≫
    (R(lowerStar (ModuleCat.{u + 1} A) j)).mapIso
      ((D(upperStar (ModuleCat.{u + 1} A) j)).mapIso e)

attribute [instance] HomologicalComplex.monoidalCategoryStruct

end AlgebraicGeometry.Etale.KFlatSupportComparison
