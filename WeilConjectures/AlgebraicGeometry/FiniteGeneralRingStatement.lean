/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingIntegrationExponent
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingOrientationSupport
public import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingSiteScalar
public import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingTensorFormula
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteNormalizedOrientationScalar
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteProCoefficientCounitTransport
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothLevelOfOrientation
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothNormalizedExistence

/-! # Smooth purity over a finite coefficient ring

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-orientation-from-the-diagonal/sk-thm-smooth-purity/
sk-thm-smooth-purity-general-ring.md`, lemma det-sp-finite-general-ring,
statement (1)--(3) and proof (1)--(3)
(blueprint: det-sp-finite-general-ring).

The statement uses the published ordinary/pro-etale constructions.  The object
`dualizingComplex A f` is the transported exceptional inverse image of the
coefficient unit, `line A N hA X d` is the ordered Tate line with shift, and
`proGamma` is the specified tensor/counit mate.  The predicate
`OrientationNormalized` records the diagonal, deformation-to-the-normal-cone,
and Kummer-normalized vector-integration construction.  The final predicate
`FiniteGeneralRingLevelIndependence` records the common-exponent comparison.

Proof steps (postponed at stage 2):

1. A field is Noetherian; finite-type permanence makes `X` and `Y` Noetherian,
   `f` quasi-compact, and smoothness gives finite type.  Nagata supplies the
   coefficient-independent compactification and `ell` is invertible on the
   schemes by the characteristic hypothesis.
2. The unital map `R = Z/ell^n → A` and the ordinary dualizing scalar map are
   fixed.  The scalar mate and its coefficient-unit identification define the
   comparison `c_{R,A}` and the counit equation in the helper below.
3. The diagonal-scalar comparison is applied to the actual diagonal and Rees
   family; its two fibre squares identify the scalar and direct deformation
   factors, with no section of `f` chosen.
4. Kummer-normalized vector integration and the projective-line splitting are
   transported through the scalar mate.  Transposition gives the scalar
   orientation equation and its inverse.
5. The bounded ordinary objects are transported across the proper/open site
   comparison.  The counit characterization identifies the transported mate
   with `c_{R,A}` and proves its invertibility at the coefficient units.
6. The ordinary smooth tensor theorem identifies the inverse projection-formula
   transpose with the specified pro-etale tensor map, so `proGamma` is the
   resulting map on intrinsic finite-Tor constructible objects.
7. The finite-ring tensor formula proves target constructibility, source
   constructibility, invertibility, and naturality of `proGamma`.
8. For a second annihilating exponent use the power map on roots of unity and
   its generator-normalized line comparison through the maximum exponent.
9. The normalized orientation is unique after the diagonal/Rees/vector-
   integration equation; tensoring with the common line comparison therefore
   identifies the complete natural transformations and proves independence of
   `n`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.ProEtale

/-- Derived scalar extension in the fixed-coefficient universe of this statement.
This is the published K-flat scalar extension, with no change of site universes.
Source: `det-sp-scalar-extension-functor`, clause (1)
(blueprint: det-sp-finite-general-ring). -/
def generalFieldScalarExtension
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (phi : A →+* B) (T : Scheme.{u}) : proCategory A T ⥤ proCategory B T :=
  Sheaf.fixedCoefficientDerivedScalarExtension (Scheme.ProEt.topology T) phi

/-- The same fixed-coefficient scalar extension on the ordinary etale site.
The published ordinary coefficient arrows have definitionally this left-adjoint interface.
Source: general-ring proof step 2 (blueprint: det-sp-finite-general-ring). -/
def generalFieldEtaleScalarExtension
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (phi : A →+* B) (T : Scheme.{u}) :
    Etale.DerivedCategoryModule A T ⥤ Etale.DerivedCategoryModule B T :=
  Sheaf.fixedCoefficientDerivedScalarExtension T.smallEtaleTopology phi

/-- Restriction of coefficients commutes with comparison inverse image: conjugate
sectionwise commutation of comparison restriction with coextension of scalars.
Source: general-ring proof step 5, scalar/site square
(blueprint: det-sp-finite-general-ring). -/
def generalFieldSheafRestrictionIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (phi : A →+* B) (T : Scheme.{u}) :
    comparisonUpperStar (ModuleCat.{u + 1} B) T ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology T) phi ≅
      Sheaf.restrictScalars T.smallEtaleTopology phi ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) T :=
  ((conjugateIsoEquiv
    ((comparisonAdjunction (ModuleCat.{u + 1} B) T).comp
      (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) phi))
    ((Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology phi).comp
      (comparisonAdjunction (ModuleCat.{u + 1} A) T))).symm (Iso.refl _)).symm

/-- Exact descent of the canonical sheaf restriction square.
Source: general-ring proof step 5, scalar/site square
(blueprint: det-sp-finite-general-ring). -/
def generalFieldRestrictionIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (phi : A →+* B) (T : Scheme.{u}) :
    comparison B T ⋙ Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) phi ≅
      Sheaf.derivedRestrictScalars T.smallEtaleTopology phi ⋙ comparison A T :=
  (Functor.mapDerivedCategoryCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} B) T)
    (Sheaf.restrictScalars (Scheme.ProEt.topology T) phi)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (generalFieldSheafRestrictionIso phi T) ≪≫
    Functor.mapDerivedCategoryCompIso (Sheaf.restrictScalars T.smallEtaleTopology phi)
      (comparisonUpperStar (ModuleCat.{u + 1} A) T)

/-- The scalar/site mate, using the fixed-coefficient derived scalar adjunction.
Both scalar functors are left adjoints to the exact restrictions in the preceding square.
Source: general-ring proof step 5, scalar/site square
(blueprint: det-sp-finite-general-ring). -/
def generalFieldScalarSiteMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (phi : A →+* B) (T : Scheme.{u}) :
    comparison A T ⋙ generalFieldScalarExtension phi T ⟶
      generalFieldEtaleScalarExtension phi T ⋙ comparison B T :=
  letI := Sheaf.fixedCoefficientDerivedRestriction_isRightAdjoint
    (Scheme.ProEt.topology T) phi
  letI := Sheaf.fixedCoefficientDerivedRestriction_isRightAdjoint T.smallEtaleTopology phi
  ((mateEquiv
    (G := comparison A T) (H := comparison B T)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology phi))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) phi))).symm
    (TwoSquare.mk _ _ _ _ (generalFieldRestrictionIso phi T).inv)).natTrans

/-- The scalar-unit map, normalized by multiplication on the ordinary coefficient unit.
Source: general-ring proof steps 2 and 5 (blueprint: det-sp-finite-general-ring). -/
def generalFieldScalarUnitMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (phi : A →+* B) (T : Scheme.{u}) :
    (generalFieldScalarExtension phi T).obj (finiteGeneralRingUnit A T) ⟶
      finiteGeneralRingUnit B T :=
  (generalFieldScalarSiteMap phi T).app (Etale.ordinaryFiniteUnit A T) ≫
    (comparison B T).map
      ((generalFieldEtaleScalarExtension phi T).mapIso
          (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T) ≪≫
        Etale.ExceptionalCoefficients.unitIso phi T ≪≫
        (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} B) T).symm).hom

private theorem scalarSite_current
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (phi : A →+* B) (T : Scheme.{u}) :
    generalFieldScalarSiteMap phi T =
      CoefficientScalarRepresentatives.comparisonMap T phi := by
  rfl

private instance scalarSite_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (phi : A →+* B) (T : Scheme.{u}) : IsIso (generalFieldScalarSiteMap phi T) := by
  rw [scalarSite_current]
  infer_instance

private theorem scalarSite_published
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (phi : A →+* B) (T : Scheme.{u}) :
    generalFieldScalarSiteMap phi T = (pbcComparisonReduction T phi).hom := by
  rfl

private theorem scalarUnit_published
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (phi : A →+* B) (T : Scheme.{u}) :
    generalFieldScalarUnitMap phi T = (finiteGeneralRingScalarUnitIso phi T).hom := by
  rw [generalFieldScalarUnitMap, scalarSite_published]
  rfl

private theorem dualizingUnit_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [HasCompactification f] :
    IsIso (finiteGeneralRingDualizingUnitMap A f) := by
  have := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} A) Y
    (Etale.ordinaryFiniteUnit A Y) (show _root_.DerivedCategory.TStructure.t.plus
      (Etale.ordinaryFiniteUnit A Y) from ⟨0, inferInstance⟩)
  unfold finiteGeneralRingDualizingUnitMap
  infer_instance

private theorem compactCoefficient_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (phi : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] (M : Etale.DerivedCategoryModule A X)
    (hM : Etale.DerivedCategory.boundedConstructibleFiniteTor A X M) :
    IsIso (proCompactCoefficientMap phi f ((comparison A X).obj M)) := by
  have hp : _root_.DerivedCategory.TStructure.t.plus ((ordinaryScalar phi X).obj M) :=
    Etale.ExceptionalCoefficients.scalar_extension_plus_of_finiteTor phi X M hM.2
  have ha : IsIso (compactSiteMap A f M) := by
    unfold compactSiteMap
    rw [dif_pos hM.1.1.1]
    infer_instance
  have hb : IsIso (compactSiteInverse B f ((ordinaryScalar phi X).obj M)) := by
    unfold compactSiteInverse
    rw [dif_pos hp]
    infer_instance
  rw [compactCoefficientAtOrigin phi f M hM]
  have := Etale.ExceptionalCoefficients.compactSupport_isIso phi
    (HasCompactification.compactification f) M
  infer_instance

private def sourceInLine (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : Etale.FiniteSmoothPurity.proCategory A Y) :
    Etale.FiniteSmoothPurity.comparison A X ⋙
        (ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((Etale.FiniteSmoothPurity.proPullback A f).obj K) ⟶
      (Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((Etale.ordinaryFinitePullback A f).obj
            ((Etale.FiniteSmoothPurity.origin A Y).obj K)) ⋙
        Etale.FiniteSmoothPurity.comparison A X := by
  let : IsNoetherianRing A := isNoetherian_of_finite A A
  let : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  exact Functor.whiskerLeft (Etale.FiniteSmoothPurity.comparison A X)
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).map
        ((Etale.FiniteSmoothPurity.proPullback A f).map
            (Etale.FiniteSmoothPurity.originInverse A Y K) ≫
          (Etale.FiniteSmoothPurity.sitePullbackIso A f).hom.app
            ((Etale.FiniteSmoothPurity.origin A Y).obj K))) ≫
    (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A)
      ((Etale.ordinaryFinitePullback A f).obj
        ((Etale.FiniteSmoothPurity.origin A Y).obj K))).inv

private theorem sourceInLine_app (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : Etale.FiniteSmoothPurity.proCategory A Y)
    (L : Etale.DerivedCategoryModule A X) :
    (sourceInLine A f K).app L = Etale.FiniteSmoothPurity.sourceToOrigin A f L K := by
  let : IsNoetherianRing A := isNoetherian_of_finite A A
  let : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  simp only [sourceInLine, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.map_comp, NatTrans.comp_app, Etale.FiniteSmoothPurity.sourceToOrigin,
    Etale.FiniteSmoothPurity.proSource, Functor.comp_map,
    Etale.FiniteSmoothPurity.sourceAtOriginIso, Iso.trans_inv,
    Category.assoc]
  rfl

private theorem gammaInLine (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {L M : Etale.DerivedCategoryModule A X} (b : M ≅ L)
    (alpha : Etale.dualizingComplex A f ≅ L)
    (K : Etale.FiniteSmoothPurity.proCategory A Y) :
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.FiniteSmoothPurity.proPullback A f).obj K)).map
          ((Etale.FiniteSmoothPurity.comparison A X).map b.hom) ≫
        Etale.FiniteSmoothPurity.proGamma A f L alpha K =
      Etale.FiniteSmoothPurity.sourceToOrigin A f M K ≫
        (Etale.FiniteSmoothPurity.comparison A X).map
          (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
              ((Etale.ordinaryFinitePullback A f).obj
                ((Etale.FiniteSmoothPurity.origin A Y).obj K))).map
                  (b.hom ≫ alpha.inv) ≫
            Etale.smoothTensorDualityMap A f
              (Etale.isIso_projectionMap_of_finite A f)
              ((Etale.FiniteSmoothPurity.origin A Y).obj K)) := by
  have hn := (sourceInLine A f K).naturality b.hom
  rw [sourceInLine_app, sourceInLine_app] at hn
  dsimp only [Functor.comp_map] at hn
  simp only [Etale.FiniteSmoothPurity.proGamma, Etale.FiniteSmoothPurity.gamma,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]

private theorem gammaOrientationEquality (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    {L L' M : Etale.DerivedCategoryModule A X} (b : M ≅ L) (b' : M ≅ L')
    (alpha : Etale.dualizingComplex A f ≅ L)
    (alpha' : Etale.dualizingComplex A f ≅ L')
    (h : alpha.hom ≫ b.inv = alpha'.hom ≫ b'.inv)
    (K : Etale.FiniteSmoothPurity.proCategory A Y) :
    ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.FiniteSmoothPurity.proPullback A f).obj K)).map
          ((Etale.FiniteSmoothPurity.comparison A X).map b.hom) ≫
        Etale.FiniteSmoothPurity.proGamma A f L alpha K =
      ((ProEtale.derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((Etale.FiniteSmoothPurity.proPullback A f).obj K)).map
          ((Etale.FiniteSmoothPurity.comparison A X).map b'.hom) ≫
        Etale.FiniteSmoothPurity.proGamma A f L' alpha' K := by
  have he : b.hom ≫ alpha.inv = b'.hom ≫ alpha'.inv := by
    have hi := congrArg Iso.inv (Iso.ext h : alpha ≪≫ b.symm = alpha' ≪≫ b'.symm)
    exact hi
  rw [gammaInLine, gammaInLine, he]

end AlgebraicGeometry.ProEtale
