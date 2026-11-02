/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
import WeilConjectures.CategoryTheory.Sites.ReductionFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat

/-! # Normalized ordinary coefficient scalar representatives

Source: Stacks 03EK, 03EL, 06YY and 07A4; the scalar and comparison constructions
in the finite-coefficient paragraph of scalar-six direct image
(blueprint: def-sp-coefficient-scalar-representatives).

These are the ordinary unbounded derived categories of module-valued sheaves.
The chosen scalar left adjoint is determined by actual derived restriction.
The representative arrow is defined by transposing the ordinary scalar unit.
The scalar adjunction is built in this module from the upstream K-flat derived
adjunctions; the module imports only upstream and Mathlib modules.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u v₁ v₂

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.CoefficientScalarRepresentatives

set_option Elab.async false


section Site

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)
  {A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)

attribute [local irreducible] scalarDerivedAdjunctionData

attribute [local irreducible] scalarDerivedAdjunction ordinaryExtension ordinaryAdjunction

/-- Sheafified sectionwise extension of scalars.
Source: Stacks 03EK (blueprint: def-sp-coefficient-scalar-representatives). -/
def ordinaryExtension : Sheaf J (ModuleCat.{u + 1} A) ⥤
    Sheaf J (ModuleCat.{u + 1} B) :=
  Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} a)

/-- The actual ordinary extension/restriction adjunction, normalized by its tensor unit.
Source: Stacks 03EK (blueprint: def-sp-coefficient-scalar-representatives). -/
def ordinaryAdjunction : ordinaryExtension J a ⊣ Sheaf.restrictScalars J a :=
  Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} a)

private noncomputable def scalarDerivedAdjunctionData
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (K : GrothendieckTopology C) (φ : R →+* S) :=
  normalizedDerivedAdjunction
    (A := Sheaf K (ModuleCat.{u + 1} R)) (B := Sheaf K (ModuleCat.{u + 1} S))
    (E := ordinaryExtension K φ) (U := Sheaf.restrictScalars K φ)
    (ordinaryAdjunction K φ)

/-- The fixed derived scalar extension, selected by its uniquely determined adjunction.
Source: Stacks 06YY (blueprint: def-sp-coefficient-scalar-representatives). -/
def extension : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)) :=
  (Sheaf.derivedRestrictScalars J a).leftAdjoint

/-- The specified scalar adjunction to actual exact derived restriction.
Source: Stacks 06YY (blueprint: def-sp-coefficient-scalar-representatives). -/
def adjunction : extension J a ⊣ Sheaf.derivedRestrictScalars J a :=
  Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J a)

/-- The canonical representative arrow: transpose the localized ordinary scalar unit.
Source: Stacks 03EK and 06YY (blueprint: def-sp-coefficient-scalar-representatives). -/
def representative
    (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ) :
    (extension J a).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((ordinaryExtension J a).mapHomologicalComplex (.up ℤ)).obj P) :=
  let PE : CochainComplex (Sheaf J (ModuleCat.{u + 1} B)) ℤ :=
    ((ordinaryExtension J a).mapHomologicalComplex (.up ℤ)).obj P
  ((adjunction J a).homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj PE)).symm
    (DerivedCategory.Q.map
      (show P ⟶ ((Sheaf.restrictScalars J a).mapHomologicalComplex (.up ℤ)).obj PE from
        (Functor.mapHomologicalComplexIdIso
          (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ)).inv.app P ≫
          (NatTrans.mapHomologicalComplex (ordinaryAdjunction J a).unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso
            (F := ordinaryExtension J a) (G := Sheaf.restrictScalars J a)
            (Iso.refl _) (.up ℤ)).inv.app P) ≫
      (Sheaf.restrictScalars J a).mapDerivedCategoryFactors.inv.app PE)

end Site

section Comparison

open AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) {A B : Type (u + 1)} [CommRing A] [CommRing B]
  (a : A →+* B)

/-- Ordinary restriction/site comparison, conjugate to the sectionwise coextension square.
Source: Stacks 03D2 and 03EL (blueprint: def-sp-coefficient-scalar-representatives). -/
def comparisonRestriction :
    ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology T) a ≅
      Sheaf.restrictScalars T.smallEtaleTopology a ⋙
        ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T :=
  ((conjugateIsoEquiv
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) T).comp
      (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) a))
    ((Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology a).comp
      (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T))).symm (Iso.refl _)).symm

/-- Exact termwise localization of the ordinary restriction/site comparison.
Source: Stacks 06YY and 07A4 (blueprint: def-sp-coefficient-scalar-representatives). -/
def derivedComparisonRestriction :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) a ≅
      Sheaf.derivedRestrictScalars T.smallEtaleTopology a ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (comparisonRestriction T a)

/-- The canonical scalar/site comparison is the inverse mate of restriction comparison.
Source: Stacks 07A4 (blueprint: def-sp-coefficient-scalar-representatives). -/
def comparisonMap :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        extension (Scheme.ProEt.topology T) a ⟶
      extension T.smallEtaleTopology a ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory :=
  ((mateEquiv (adjunction T.smallEtaleTopology a)
    (adjunction (Scheme.ProEt.topology T) a)).symm
      (TwoSquare.mk _ _ _ _ (derivedComparisonRestriction T a).inv)).natTrans

section ComparisonProof

variable {R S : Type (u + 1)} [CommRing R] [CommRing S]

attribute [local irreducible] comparisonRestriction

end ComparisonProof

/-- Regard that very mate as the tensor/site isomorphism.
Source: Stacks 07A4 (blueprint: def-sp-coefficient-scalar-representatives). -/
def comparisonIso :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory ⋙
        extension (Scheme.ProEt.topology T) a ≅
      extension T.smallEtaleTopology a ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory :=
  asIso (comparisonMap T a)

end Comparison

end AlgebraicGeometry.CoefficientScalarRepresentatives
