/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.CoefficientSystemDerivedImage.CoefficientSystemImageData
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Submission.WeilConjectures.CategoryTheory.GeometricRingInverseImage
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Submission.WeilConjectures.CategoryTheory.InverseImageRingFunctor
import Submission.WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresObjects
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.Ring
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Submission.WeilConjectures.CategoryTheory.RouteInverseImageConstantComparison
import Mathlib.CategoryTheory.Sites.Adjunction
import Submission.WeilConjectures.CategoryTheory.RouteInverseImageConstantRingOperations
import Submission.WeilConjectures.CategoryTheory.RouteInverseImageConstantSetComparison
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Sites.Limits
import Submission.WeilConjectures.CategoryTheory.RouteInverseImageConstantRingAssembly
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Adjunction.Additive
import Submission.WeilConjectures.Algebra.Homology.InverseImageScalarRestriction.InverseImageScalarRestrictionComparison
import all Submission.WeilConjectures.CategoryTheory.Sites.GeometricFreeModuleHomEquivalence
import all Submission.WeilConjectures.CategoryTheory.Sites.FreeModuleSheafConstruction
import all Submission.WeilConjectures.CategoryTheory.Sites.GeometricMorphism
import all Mathlib.CategoryTheory.Adjunction.Mates
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Sites.Sheaf
import all Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Types.Basic
import all Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Mathlib.LinearAlgebra.FreeModule.Basic
import all Submission.WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import all Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all Submission.WeilConjectures.CategoryTheory.RingedToposRingData
import all Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Submission.WeilConjectures.CategoryTheory.GeometricMorphism.GeometricInverseImageExactSupplement

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Ordinary geometric images of strict coefficient systems

Source: Zheng, Construction 4.1; Stacks Project, Tags 03DA and 03DB.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v u' v' w d
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (O : Type w) [CommRing O] (ell : O)

variable {D : Type u'} [Category.{v'} D] [EssentiallySmall.{w} C]
  [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
  (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)

/-- Levelwise ordinary lifts, before forming the category of strict systems.
Source: Stacks 03D7; Zheng Construction 4.1
(blueprint: lem-pur-coefficient-level-ordinary-images). -/
structure CoefficientLevelOrdinaryImage where
  singleton : L.obj ((constantSheaf J (Type w)).obj PUnit) ≅
    (constantSheaf K (Type w)).obj PUnit
  lift : ∀ n, AlgebraicInverseImage L
    (coefficientQuotientSheaf (J := J) O ell n)
    (coefficientQuotientSheaf (J := K) O ell n)
  constants : ∀ n x,
    L.map (coefficientConstantSection (J := J) O ell n x) ≫ (lift n).ringUnderlying.hom =
      singleton.hom ≫ coefficientConstantSection (J := K) O ell n x
  [inverseAdditive : ∀ n, (lift n).modules.Additive]
  inverseExact : ∀ n, PreservesFiniteLimits (lift n).modules ∧
    PreservesFiniteColimits (lift n).modules
  right : ∀ n, coefficientLevelModules (J := K) O ell n ⥤
    coefficientLevelModules (J := J) O ell n
  [rightAdditive : ∀ n, (right n).Additive]
  rightUnderlying : ∀ n, right n ⋙ coefficientUnderlying (J := J) O ell n ≅
    coefficientUnderlying (J := K) O ell n ⋙ V
  levelAdj : ∀ n, (lift n).modules ⊣ right n
  levelTranspose : ∀ n M N (f : (lift n).modules.obj M ⟶ N),
    (coefficientUnderlying (J := J) O ell n).map ((levelAdj n).homEquiv M N f) ≫
      (rightUnderlying n).hom.app N =
    adj.homEquiv _ _ ((lift n).moduleUnderlying.inv.app M ≫
      (coefficientUnderlying (J := K) O ell n).map f)
  restrictInverse : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientRestriction (J := J) O ell h ⋙ (lift m).modules ≅
      (lift n).modules ⋙ coefficientRestriction (J := K) O ell h
  restrictInverseUnderlying : ∀ {m n : ℕ} (h : n ≤ m) M,
    (coefficientUnderlying (J := K) O ell m).map ((restrictInverse h).hom.app M) ≫
      (coefficientRestrictionUnderlying (J := K) O ell h).hom.app
        ((lift n).modules.obj M) ≫ (lift n).moduleUnderlying.hom.app M =
    (lift m).moduleUnderlying.hom.app ((coefficientRestriction (J := J) O ell h).obj M) ≫
      L.map ((coefficientRestrictionUnderlying (J := J) O ell h).hom.app M)
  restrictRight : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientRestriction (J := K) O ell h ⋙ right m ≅
      right n ⋙ coefficientRestriction (J := J) O ell h
  restrictTranspose : ∀ {m n : ℕ} (h : n ≤ m) M N
    (f : (lift n).modules.obj M ⟶ N),
    (levelAdj m).homEquiv _ _
      ((restrictInverse h).hom.app M ≫ (coefficientRestriction (J := K) O ell h).map f) =
    (coefficientRestriction (J := J) O ell h).map ((levelAdj n).homEquiv _ _ f) ≫
      (restrictRight h).inv.app N

attribute [instance] CoefficientLevelOrdinaryImage.inverseAdditive
  CoefficientLevelOrdinaryImage.rightAdditive

end SheafOfModules
