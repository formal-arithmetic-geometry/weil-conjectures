/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import all WeilConjectures.CategoryTheory.GeometricRingInverseImage
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.Algebra.Category.Ring.Colimits
import all Mathlib.Algebra.Category.Ring.FilteredColimits
import all WeilConjectures.CategoryTheory.InverseImageRingFunctor
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresObjects
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.RouteInverseImageConstantComparison
import all Mathlib.CategoryTheory.Sites.Adjunction
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RouteInverseImageConstantRingOperations
import all WeilConjectures.CategoryTheory.RouteInverseImageConstantSetComparison
import all Mathlib.CategoryTheory.Sites.GlobalSections
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.CategoryTheory.RouteInverseImageConstantRingAssembly
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Constant ring inverse images in an independent coefficient universe

Source: Stacks Project, Tags 00YV and 03D2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe w uC vC uD vD
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace SheafOfModules.CoefficientConstantImages

attribute [local instance] typeLimits typeSheafify

attribute [local instance] ringSmallArrowLimits typeSmallArrowLimits

attribute [local instance] ringForgetSheafification

section CoefficientConstruction
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
variable (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
variable (R : Sheaf K (Type w) ⥤ Sheaf J (Type w))
variable (adj : L ⊣ R) [PreservesFiniteLimits L]

@[reassoc] private theorem constantComparison_naturality (X Y : Type w) (f : X ⟶ Y) :
    L.map ((constantSheaf J (Type w)).map f) ≫
        (constantComparison J K L R adj).hom.app Y =
      (constantComparison J K L R adj).hom.app X ≫ (constantSheaf K (Type w)).map f :=
  (constantComparison J K L R adj).hom.naturality f

variable (Λ : Type w) [CommRing Λ] [HasWeakSheafify J CommRingCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}]

end CoefficientConstruction

section Existence
open SheafOfModules.GeometricConstruction CategoryTheory.MonoidalCategory
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
  [HasWeakSheafify J CommRingCat.{w}] [HasWeakSheafify K CommRingCat.{w}]
  [J.PreservesSheafification (CategoryTheory.forget CommRingCat.{w})]
  [K.PreservesSheafification (CategoryTheory.forget CommRingCat.{w})]
  (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
  (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)
  [PreservesFiniteLimits L]

end Existence
end SheafOfModules.CoefficientConstantImages
