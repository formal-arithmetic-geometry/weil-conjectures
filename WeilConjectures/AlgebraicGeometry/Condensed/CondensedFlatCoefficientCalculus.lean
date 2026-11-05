/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientComparisons
import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedFiniteModelProofAPISupplement
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Exact condensed coefficient changes and their derived tensor calculus

Source: archived master ModuleObject/Colimit/Compatibility.lean, A0.2 and Flat;
ModuleObject/Colimit/TwoColimit.lean, ExtendScalars
(blueprint: lem-weil-pbc-condensed-flat-coefficient-calculus).

All modules below are the master internal module objects. The constructible categories
are `PadicSubfieldConstructible` and `PadicAlgClConstructible`, with no completeness
condition. The adjunctions are on the ambient unbounded derived categories.
-/

@[expose] public section

universe u wC wD wE vC vD vE uC uD uE

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

-- Keep canonical resolution comparisons opaque to implicit instance matching.
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.CommShift.ofIso CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.extendScalars

section FiniteBasisConstruction

universe v₁ v₂ u₁ u₂
open CategoryTheory.MonObj CategoryTheory.BraidedCategory
open scoped CategoryTheory.Obj
set_option backward.isDefEq.respectTransparency false

/- The following finite free comparisons use only additive monoidal functors, so they apply
both to sheafification and to inverse image from the point. -/
namespace CategoryTheory.Mod

section Map
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  [Abelian D] [MonoidalPreadditive D]
  (F : C ⥤ D) [F.LaxMonoidal] [F.Additive]
  {R S : C} [MonObj R] [MonObj S]
  (a : R ⟶ S) [IsMonHom a]

end Map
section RingIso
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [Abelian C] [MonoidalPreadditive C] [MonoidalClosed C]
  {R S : C} [MonObj R] [MonObj S]

variable {R' S' : C} [MonObj R'] [MonObj S']
end RingIso
end CategoryTheory.Mod

/- Work sectionwise before sheafification: a continuous field-linear map gives an internal
module morphism, and the coordinate maps of a finite basis give inverse biproduct maps. -/
namespace Profinite

end Profinite

end FiniteBasisConstruction

section ModuleCacheScope

-- Package the canonical module structures once, before substituting coefficient rings.
namespace CategoryTheory
section ModuleStructures
variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{vC} C] [Abelian.HasFunctorialFlatResolution C]

end ModuleStructures
end CategoryTheory

attribute [local instance 2000] CategoryTheory.scalarAbelian
attribute [local instance 2000] CategoryTheory.scalarMonoidal
attribute [local instance 2000] CategoryTheory.scalarMonoidalAdditive
attribute [local instance 2000] CategoryTheory.scalarGrothendieck
attribute [local instance 2000] CategoryTheory.scalarCountable
attribute [local instance 2000] CategoryTheory.scalarIntColimits
attribute [local instance 2000] CategoryTheory.scalarExactIntColimits
attribute [local instance 2000] CategoryTheory.scalarFlatResolution
attribute [local instance 2000] CategoryTheory.scalarTensor4
attribute [local instance 2000] CategoryTheory.scalarTensor12
attribute [local instance 2000] CategoryTheory.scalarTensor23
attribute [local instance 2000] CategoryTheory.scalarTensorColimits
attribute [local instance 2000] CategoryTheory.scalarFlipTensorColimits

section CoherenceTools

set_option maxRecDepth 2048

namespace CategoryTheory
section
variable {C D : Type*} [Category C] [Category D]
  {F F' : C ⥤ D} {G G' : D ⥤ C}
end
end CategoryTheory

namespace CategoryTheory
section Scalar
variable {C : Type*} [Category C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S U : C} [MonObj R] [MonObj S] [MonObj U]
  [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ U) [IsMonHom ψ]
  (χ : R ⟶ U) [IsMonHom χ] (h : φ ≫ ψ = χ)

end Scalar
end CategoryTheory

namespace CategoryTheory
section ScalarCoherence
variable {C : Type*} [Category C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S U V : C} [MonObj R] [MonObj S] [MonObj U] [MonObj V]
  [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj U]
  (f : R ⟶ S) [IsMonHom f] (g : S ⟶ U) [IsMonHom g] (j : U ⟶ V) [IsMonHom j]
  (fg : R ⟶ U) [IsMonHom fg] (gj : S ⟶ V) [IsMonHom gj]
  (fgj : R ⟶ V) [IsMonHom fgj]
  (hfg : f ≫ g = fg) (hgj : g ≫ j = gj) (hfgj : f ≫ gj = fgj) (hfgj' : fg ≫ j = fgj)
end ScalarCoherence
end CategoryTheory

namespace CategoryTheory
section ScalarUnit
variable {C : Type*} [Category C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]

end ScalarUnit
end CategoryTheory

namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section DerivedComposition
variable {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
  [Abelian C] [Abelian D] [Abelian E] [Abelian V]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory V]
  {F : C ⥤ D} {G : D ⥤ E} {H : E ⥤ V} {FG : C ⥤ E} {GH : D ⥤ V} {FGH : C ⥤ V}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [FG.Additive] [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
  [GH.Additive] [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
  [FGH.Additive] [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]

end DerivedComposition
end CategoryTheory.Functor

namespace CategoryTheory.Functor
section Transport
variable {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
  {F F' : C ⥤ D} {G G' : D ⥤ E} {H H' : E ⥤ V}
  {FG FG' : C ⥤ E} {GH GH' : D ⥤ V} {FGH FGH' : C ⥤ V}

end Transport
end CategoryTheory.Functor

namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section DerivedUnit
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {A : C ⥤ C} {B : D ⥤ D} {F : C ⥤ D}
  [A.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

end DerivedUnit
end CategoryTheory.Functor

namespace CategoryTheory.Functor
section TransportUnit
variable {C D : Type*} [Category C] [Category D]
  {A A' : C ⥤ C} {B B' : D ⥤ D} {F F' : C ⥤ D}

end TransportUnit
end CategoryTheory.Functor

namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section LeftTransport
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]

variable [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

variable [MonoidalCategory E] [MonoidalPreadditive E]
  [HasCountableCoproducts E]
  [HasColimitsOfShape ℤ E] [HasExactColimitsOfShape ℤ E]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ E), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ E), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ E), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : E), PreservesColimitsOfShape ℤ ((curriedTensor E).obj X)]
  [∀ (X : E), PreservesColimitsOfShape ℤ ((curriedTensor E).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution E]
  {V : Type*} [Category V] [Abelian V] [HasDerivedCategory V]

end LeftTransport
end CategoryTheory.Functor

namespace CategoryTheory.Functor
section IdentityShift
variable (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]

end IdentityShift
end CategoryTheory.Functor

namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section LeftShift
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]

variable [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

end LeftShift
end CategoryTheory.Functor

namespace CategoryTheory
section ScalarDerived
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{vC} C] [Abelian.HasFunctorialFlatResolution C]
  {R S U V : C} [MonObj R] [MonObj S] [MonObj U] [MonObj V]
  [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj U] [IsCommMonObj V]
  [HasDerivedCategory.{vC} (Mod C R)] [HasDerivedCategory.{vC} (Mod C S)]
  [HasDerivedCategory.{vC} (Mod C U)] [HasDerivedCategory.{vC} (Mod C V)]

end ScalarDerived
end CategoryTheory

end CoherenceTools

end ModuleCacheScope

namespace AlgebraicGeometry.ProEtale

open Scheme
open CategoryTheory.MonObj CategoryTheory.Functor
open scoped CategoryTheory.Obj CategoryTheory.Functor

section FiniteFree

set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

end FiniteFree

-- Keep the resolution constructions behind their proved comparison API.

end AlgebraicGeometry.ProEtale
