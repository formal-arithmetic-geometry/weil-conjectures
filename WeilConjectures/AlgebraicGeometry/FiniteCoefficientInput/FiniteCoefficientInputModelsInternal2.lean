/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatConstructibleModel

/-! # Finite coefficient input models in internal modules

Source: current blueprint, det-sp-reduction-exceptional, proof paragraph Charts,
finite coefficient extension on bounded flat inputs.
(blueprint: lem-sp-finite-coefficient-input-models).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.FiniteCoefficientInput

open ProEtale ProEtale.FiniteDiscreteOrdinary

variable {A B : Type u} [CommRing A] [CommRing B]
  [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A]
  [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B]

/-- The same exact inverse image on unbounded derived categories.
Source: current blueprint, Charts, etale-origin input
(blueprint: lem-sp-finite-coefficient-input-models). -/
abbrev derivedSite {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {X : Scheme.{u}} (E : Encoding R X) :=
  (ordinaryPull R X).mapDerivedCategory ⋙
    E.fixedDerived.inverse

/-- The derived comparison uses the recorded ordinary scalar-adjunction mate, conjugated
by the same normalized section-action scalar comparison.
Source: current blueprint, Charts, canonical scalar/site comparison
(blueprint: lem-sp-finite-coefficient-input-models). -/
def derivedComparison {X : Scheme.{u}} {EA : Encoding A X} {EB : Encoding B X}
    {φ : A →+* B}
    (s : FiniteInputScalarCoordinates φ (coefficientHom φ) X EA EB)
    (L : Etale.DerivedCategoryModule (ULift.{u + 1} A) X) :
    (derivedExtension φ X).obj ((derivedSite EA).obj L) ⟶
      (derivedSite EB).obj
        ((CoefficientScalarRepresentatives.extension X.smallEtaleTopology
          (RingHom.ulift.{u + 1, u + 1} φ)).obj L) :=
  EB.fixedDerived.unitIso.hom.app _ ≫ EB.fixedDerived.inverse.map
    (s.fixedExtension.hom.app _ ≫
      (CoefficientScalarRepresentatives.extension (Scheme.ProEt.topology X)
        (RingHom.ulift.{u + 1, u + 1} φ)).map
          (EA.fixedDerived.counitIso.hom.app _) ≫
      (CoefficientScalarRepresentatives.comparisonMap X (RingHom.ulift.{u + 1, u + 1} φ)).app L)

/-- Canonical exact-localization representative of the internal site inverse image.
Source: current blueprint, Charts, localization of the etale-origin model
(blueprint: lem-sp-finite-coefficient-input-models). -/
def siteRepresentative {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {X : Scheme.{u}} (E : Encoding R X)
    (P : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ) :
    (derivedSite E).obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj (((site E).mapHomologicalComplex (.up ℤ)).obj P) :=
  E.fixedDerived.inverse.map
      ((ordinaryPull R X).mapDerivedCategoryFactors.hom.app P) ≫
    (heart E).inverse.mapDerivedCategoryFactors.hom.app _

/-- Ordinary etale scalar extension, applied termwise to the chosen input model.
Source: current blueprint, Charts, bounded flat input
(blueprint: lem-sp-finite-coefficient-input-models). -/
abbrev etaleComplex (φ : A →+* B) (X : Scheme.{u}) :=
  (CoefficientScalarRepresentatives.ordinaryExtension X.smallEtaleTopology
        (RingHom.ulift.{u + 1, u + 1} φ)).mapHomologicalComplex (.up ℤ)

/-- The exact internal site inverse image, applied to complexes termwise.
Source: current blueprint, Charts, bounded flat input
(blueprint: lem-sp-finite-coefficient-input-models). -/
abbrev siteComplex {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    {X : Scheme.{u}} (E : Encoding R X) := (site E).mapHomologicalComplex (.up ℤ)

/-- The genuine internal balanced scalar extension, applied termwise.
Source: current blueprint, Charts, bounded flat input
(blueprint: lem-sp-finite-coefficient-input-models). -/
abbrev extensionComplex (φ : A →+* B) (X : Scheme.{u}) :=
  (extension φ X).mapHomologicalComplex (.up ℤ)

/-- The exact ordinary comparison localized termwise, in the fixed-scalar presentation.
Source: current blueprint, Charts (blueprint: lem-sp-finite-coefficient-input-models). -/
abbrev ordinaryDerivedSite (R : Type u) [CommRing R] (X : Scheme.{u}) :=
  (ordinaryPull R X).mapDerivedCategory

/-- Ordinary unbounded scalar extension on the pro-etale site.
Source: current blueprint, Charts (blueprint: lem-sp-finite-coefficient-input-models). -/
abbrev ordinaryDerivedExtension (φ : A →+* B) (X : Scheme.{u}) :=
  CoefficientScalarRepresentatives.extension (Scheme.ProEt.topology X)
    (RingHom.ulift.{u + 1, u + 1} φ)

end AlgebraicGeometry.FiniteCoefficientInput
