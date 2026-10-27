/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import Sheaf.AlgebraicGeometry.EtaleKFlatSupportData
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.AlgebraicGeometry.EtaleDerivedChainTranspose
public import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
public import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Sheaf.Paper.EtaleDerivedScalarTensor


/-! # Canonical open cochain tensor map

Canonical representative comparisons for the open tensor model.

Source: Stacks Project, sites-cohomology.tex, Tags 0FPI, 07A4 and 06YS,
with the tensor/scalar specialization in the DAG proof
(blueprint: def-pur-kflat-open-model-maps).

The ordinary adjunct and localization comparisons below use the published
cochain adjunction and the canonical derived comparison.
No strict B-action on a representative is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v w u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.KFlatOpenProjection

/-- The ordinary tensor adjunct on cochain complexes, before specialization.
Source: Stacks 07A4, 0FPI (blueprint: def-pur-kflat-open-model-maps). -/
def cochainAdjunct
    {C : Type u} {D : Type w} [Category.{v} C] [Category.{v₂} D]
    [Abelian C] [Abelian D]
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v₂} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [MonoidalClosed C] [MonoidalClosed D]
    [BraidedCategory C] [BraidedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [F.Monoidal] [F.IsLeftAdjoint] (adj : F ⊣ G)
    (Q I J : CochainComplex C ℤ) (a : Q ⊗ I ⟶ J) :=
  KFlatSupportComparison.tensorAdjunct (adj.mapHomologicalComplex (.up ℤ)) Q I J a

attribute [local irreducible] Sheaf.monoidalCategory
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar
  upperStarLowerStarAdjunction Functor.mapHomologicalComplex


variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
  {U P : Scheme.{u}}

/-- The actual cochain composite j_*j^*, with no derived replacement.
Source: Stacks 0FPI (blueprint: def-pur-kflat-open-model-maps). -/
def openComplex (j : U ⟶ P)
    (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  ((lowerStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj
    (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj I)

/-- The canonical comparison for the exact pullback, with its localization factors.
Source: Stacks 07A4 and 0FPI (blueprint: def-pur-kflat-open-model-maps). -/
def pullbackRepresentativeIso (j : U ⟶ P)
    (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    L(upperStar (ModuleCat.{u + 1} A) j).obj (_root_.DerivedCategory.Q.obj I) ≅
      _root_.DerivedCategory.Q.obj
        (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj I) :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).app _ ≪≫
    (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.app I

/-- The ordinary adjunct v of c_(Q,C), tensor of the ordinary counit, c_(Q,I)^(-1),
and j^*a, in that order. The total tensor and comparison are the signed ones.
Source: Stacks 07A4 and 0FPI (blueprint: def-pur-kflat-open-model-maps). -/
def ordinaryMap (j : U ⟶ P) :=
  cochainAdjunct (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j)


/-- The specified canonical comparison for C=j_*j^*I, followed by j^*(ell I)=j^*L.
Source: Stacks 0FPI (blueprint: def-pur-kflat-open-model-maps). -/
def directImageIdentification (j : U ⟶ P)
    (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (L : DerivedCategoryModule A P) (eI : _root_.DerivedCategory.Q.obj I ≅ L)
    [IsIso ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorUnitQ
      (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj I))] :
    _root_.DerivedCategory.Q.obj (openComplex j I) ≅
      R(lowerStar (ModuleCat.{u + 1} A) j).obj
        (L(upperStar (ModuleCat.{u + 1} A) j).obj L) :=
  asIso ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorUnitQ
    (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj I)) ≪≫
    R(lowerStar (ModuleCat.{u + 1} A) j).mapIso
      ((pullbackRepresentativeIso j I).symm ≪≫
        L(upperStar (ModuleCat.{u + 1} A) j).mapIso eI)


end AlgebraicGeometry.Etale.KFlatOpenProjection
