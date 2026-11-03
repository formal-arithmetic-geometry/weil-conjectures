/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.Algebra.Homology.BifunctorFlip
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Localization.Predicate
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.Picard.SiteDerivedTensorDescentIndependentCoefficients

/-! # Flat degree-zero tensor and unbounded cohomology on a ringed site

Source: Stacks Project, sites-cohomology.tex, Tags 06YN, 06YS, 06YU and its preceding
localization construction; homology.tex, Tag 010N, exact functors on abelian categories.
(blueprint: lem-fd-ringed-flat-single-tensor-cohomology)

The derived-object comparison is included before its cohomology comparisons. All tensors
and representative comparisons are the published site-derived-tensor constructions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SheafOfModules.KFlatFixedTensor

namespace SheafOfModules.FlatSingleTensor

variable {S : Type u} [Category.{v} S] [EssentiallySmall.{r} S]
  {J : GrothendieckTopology S} (R : Sheaf J CommRingCat.{r})

variable [HasDerivedCategory.{w} (Modules R)]

set_option allowUnsafeReducibility true in
attribute [local irreducible] derivedTensor
attribute [local irreducible] siteDerivedTensorIndependentCoefficients representativeIso

omit [HasDerivedCategory (Modules R)] in
omit [HasDerivedCategory (Modules R)] in
section GenericCollapse

variable {M : Type*} [Category* M] [Preadditive M] [HasZeroObject M]
  (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
  [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in

/-- The existing degree-zero complex functor, with no replacement of its data.
Source: Stacks, Tag 06YU (blueprint: lem-fd-ringed-flat-single-tensor-cohomology). -/
abbrev degreeZero : Modules R ⥤ CochainComplex (Modules R) ℤ :=
  HomologicalComplex.single (Modules R) (.up ℤ) 0

/-- The published K-flat derived tensor with the localized degree-zero right factor.
Source: Stacks, Tag 06YU (blueprint: lem-fd-ringed-flat-single-tensor-cohomology). -/
abbrev derivedRight (L : Modules R) : DerivedCategory (Modules R) ⥤
    DerivedCategory (Modules R) :=
  (derivedTensor R).flip.obj (DerivedCategory.Q.obj ((degreeZero R).obj L))

/-- The map of the published derived bifunctor on an arbitrary derived and module map.
Source: Stacks, Tag 06YU (blueprint: lem-fd-ringed-flat-single-tensor-cohomology). -/
abbrev derivedMap {K K' : DerivedCategory (Modules R)} (f : K ⟶ K')
    {L L' : Modules R} (g : L ⟶ L') :
    (derivedRight R L).obj K ⟶ (derivedRight R L').obj K' :=
  (Functor.uncurry.obj (derivedTensor R)).map
    (X := (K, DerivedCategory.Q.obj ((degreeZero R).obj L)))
    (Y := (K', DerivedCategory.Q.obj ((degreeZero R).obj L')))
    (f, DerivedCategory.Q.map ((degreeZero R).map g))

@[reassoc] private theorem collapse_ι (L : M) (E : CochainComplex M ℤ) (i : ℤ) :
    HomologicalComplex.ιMapBifunctor E ((CochainComplex.singleFunctor _ 0).obj L)
        T (.up ℤ) i 0 i (Int.add_zero i) ≫
      (CochainComplex.mapBifunctorSingle₂Iso T L E).hom.f i =
        (T.obj (E.X i)).map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom := by
  dsimp [CochainComplex.mapBifunctorSingle₂Iso, CochainComplex.mapBifunctorSingle₁Iso,
    HomologicalComplex.Hom.isoOfComponents]
  erw [HomologicalComplex.ι_mapBifunctorFlipIso_inv_assoc]
  simp [CochainComplex.mapBifunctorSingle₁XIso, HomologicalComplex.singleObjXSelf]

set_option backward.isDefEq.respectTransparency false in
end GenericCollapse

omit [HasDerivedCategory (Modules R)] in
omit [HasDerivedCategory (Modules R)] in
set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory (Modules R)] in
set_option backward.isDefEq.respectTransparency false in
set_option allowUnsafeReducibility true in
attribute [local irreducible] totalTensor ordinaryTensor
attribute [local irreducible] cohomologyComparison

set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory (Modules R)] in
set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] derivedCohomologyIso localizedComparison cohomologyNatIso

set_option backward.isDefEq.respectTransparency false in
end SheafOfModules.FlatSingleTensor
