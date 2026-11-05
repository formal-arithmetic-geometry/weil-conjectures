/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryRealization
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.Tensor.TensorComparisonModelPreservesFlat
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.AlgebraicGeometry.Tensor.TensorComparisonCochainSquare
import all WeilConjectures.AlgebraicGeometry.System.SystemTensorReductionFormula

/-! # Evaluation compatibility of representative-normalized tensor comparisons

Source: Zheng Construction 4.1; Stacks 06YU and 07A4.
(blueprint: lem-coef-semilinear-geometric-tensor-evaluation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard DerivedCategory SheafOfModules.monoidalCategory
  CoefficientClosedStructure.tensor

section FlatPreservation
variable {C₀ C₁ : Type c} [Category.{v} C₀] [Category.{v} C₁]
  [EssentiallySmall.{max c v r} C₀] [EssentiallySmall.{max c v r} C₁]
  (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
  (R₀ : Sheaf J₀ CommRingCat.{max c v r}) (R₁ : Sheaf J₁ CommRingCat.{max c v r})

end FlatPreservation

section FourModels
variable {C₀ C₁ C₂ C₃ : Type c}
  [Category.{v} C₀] [Category.{v} C₁] [Category.{v} C₂] [Category.{v} C₃]
  [EssentiallySmall.{max c v r} C₀] [EssentiallySmall.{max c v r} C₁]
  [EssentiallySmall.{max c v r} C₂] [EssentiallySmall.{max c v r} C₃]
  (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
  (J₂ : GrothendieckTopology C₂) (J₃ : GrothendieckTopology C₃)
  (R₀ : Sheaf J₀ CommRingCat.{max c v r}) (R₁ : Sheaf J₁ CommRingCat.{max c v r})
  (R₂ : Sheaf J₂ CommRingCat.{max c v r}) (R₃ : Sheaf J₃ CommRingCat.{max c v r})
  (F : Mod.{c, v, max c v r} J₀ R₀ ⥤ Mod.{c, v, max c v r} J₁ R₁)
  (G : Mod.{c, v, max c v r} J₁ R₁ ⥤ Mod.{c, v, max c v r} J₃ R₃)
  (H : Mod.{c, v, max c v r} J₀ R₀ ⥤ Mod.{c, v, max c v r} J₂ R₂)
  (I : Mod.{c, v, max c v r} J₂ R₂ ⥤ Mod.{c, v, max c v r} J₃ R₃)
  [F.Additive] [G.Additive] [H.Additive] [I.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
  (S₀ : Closed.{c, v, r} J₀ R₀) (S₁ : Closed.{c, v, r} J₁ R₁)
  (S₂ : Closed.{c, v, r} J₂ R₂) (S₃ : Closed.{c, v, r} J₃ R₃)
  (T₀ : Models.{c, v, r} J₀ R₀ S₀) (T₁ : Models.{c, v, r} J₁ R₁ S₁)
  (T₂ : Models.{c, v, r} J₂ R₂ S₂) (T₃ : Models.{c, v, r} J₃ R₃ S₃)
  (μF : S₀.tensor ⋙ F.mapDerivedCategory ≅
    (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ S₁.tensor)
  (μG : S₁.tensor ⋙ G.mapDerivedCategory ≅
    (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ S₃.tensor)
  (μH : S₀.tensor ⋙ H.mapDerivedCategory ≅
    (H.mapDerivedCategory.prod H.mapDerivedCategory) ⋙ S₂.tensor)
  (μI : S₂.tensor ⋙ I.mapDerivedCategory ≅
    (I.mapDerivedCategory.prod I.mapDerivedCategory) ⋙ S₃.tensor)
  (tF : TensorComparisonModel.{c, v, r} J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁ μF)
  (tG : TensorComparisonModel.{c, v, r} J₁ J₃ R₁ R₃ G S₁ S₃ T₁ T₃ μG)
  (tH : TensorComparisonModel.{c, v, r} J₀ J₂ R₀ R₂ H S₀ S₂ T₀ T₂ μH)
  (tI : TensorComparisonModel.{c, v, r} J₂ J₃ R₂ R₃ I S₂ S₃ T₂ T₃ μI)
  (θ : F ⋙ G ≅ H ⋙ I)
  (ho : ∀ M N,
    G.map (tF.ordinary M N).hom ≫ (tG.ordinary (F.obj M) (F.obj N)).hom ≫
      ordinaryTensorHom.{c, v, r} J₃ R₃ (θ.hom.app M) (θ.hom.app N) =
    θ.hom.app (ordinaryTensor.{c, v, r} J₀ R₀ M N) ≫
      I.map (tH.ordinary M N).hom ≫ (tI.ordinary (H.obj M) (H.obj N)).hom)

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
-- Keep this composite isomorphism intact during reassociation.
@[irreducible] private def twoFactors (P : CochainComplex (Mod.{c, v, max c v r} J₀ R₀) ℤ) :
    G.mapDerivedCategory.obj (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) :=
  G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app P) ≪≫
    G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj P)

end FourModels

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)

variable (A : Data.{c, v, r} J B τ)
  (O : GeometryOrdinary.{c, v, r} J B τ J' uInv uPush adjSet)
  (target : Data.{c, v, r} J' O.coefficients O.coefficientTransition)

end WeilConjectures.SemilinearSections
