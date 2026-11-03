/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordered.OrderedAffineTraceNormalForm
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.ChartScalarReassociation
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

/-! Expanded site-side maps for the finite affine scalar transport calculation.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md`, Charts.
(blueprint: def-sp-finite-affine-site-scalar-data). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The etale chart operation before its final shift. -/
abbrev siteEtalePreOperation (R : Type (u + 1)) [CommRing R]
    (N : ℕ) (hR : (N : R) = 0) {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) :=
  (upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory ⋙
    (derivedTensor (ModuleCat.{u + 1} R) X).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateTwist X N R hR d))

/-- The pro-etale chart operation before its final shift. -/
abbrev siteProPreOperation (R : Type (u + 1)) [CommRing R]
    (N : ℕ) (hR : (N : R) = 0) {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} R) f).mapDerivedCategory ⋙
    (ProEtale.derivedTensor (ModuleCat.{u + 1} R) X).obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateTwist X N R hR d)))

/-- The pullback and tensor part of the specified chart comparison. -/
def sitePreComparison (R : Type (u + 1)) [CommRing R] [Finite R]
    (N : ℕ) (hR : (N : R) = 0) {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) S).mapDerivedCategory ⋙
        siteProPreOperation R N hR f d ≅
      siteEtalePreOperation R N hR f d ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} R) f) ≪≫
        Functor.mapDerivedCategoryCompIso _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        (ModuleCat.{u + 1} R)
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateTwist X N R hR d))).symm ≪≫
    (Functor.associator _ _ _).symm

/-- The tensor, Tate and pullback part of the etale scalar chart map. -/
abbrev siteEtalePreScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) (K : DerivedCategoryModule A S) :
    (scalarExtension φ X).obj ((siteEtalePreOperation A N hA f d).obj K) ⟶
      (siteEtalePreOperation B N hB f d).obj ((scalarExtension φ S).obj K) :=
  (ExceptionalCoefficients.tensorIso φ X).hom.app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateTwist X N A hA d),
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K) ≫
    derivedTensorHom (ModuleCat.{u + 1} B) (finiteAffineTateScalarMap φ X N hA hB d)
      ((finiteAffineExactPullbackScalarIso φ f).hom.app K)

/-- The tensor, Tate and pullback part of the pro-etale scalar chart map. -/
abbrev siteProPreScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))) :=
  ProEtale.chartPreScalarReassociationMap φ N hA hB f d K

end AlgebraicGeometry.Etale
