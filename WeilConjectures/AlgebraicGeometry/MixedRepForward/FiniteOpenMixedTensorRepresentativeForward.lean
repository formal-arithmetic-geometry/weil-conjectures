/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorSheaf
import WeilConjectures.CategoryTheory.FiniteOpenMixedTensorRepresentativeCounit
import WeilConjectures.CategoryTheory.FiniteOpenMixedTensorRepresentativeCounitTransport
import WeilConjectures.AlgebraicGeometry.MixedRepForward.ForwardTransportGeneral

/-!
# The forward cochain tensor counit square

Source: Stacks Project, sites-cohomology.tex, Tag 07A4, tensor pullback comparison.
Unpack the defining equation of the published comparison on homotopy objects. Its two
counits are the tensor of the pullback counits followed by the target tensorator, and
the source tensorator followed by the pullback counit. Evaluate at the homotopy
quotients of the two complexes, expand the native cochain tensorator transport, and
identify the pullback counits with the canonical exact-derived factors.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor
section QuotientIdentities

universe w

private theorem quotient_tensor
    {C : Type*} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    (P Q : CochainComplex C ℤ) :
    ((HomotopyCategory.quotient C (.up ℤ)).obj P ⊗
      (HomotopyCategory.quotient C (.up ℤ)).obj Q) =
      (HomotopyCategory.quotient C (.up ℤ)).obj (P ⊗ Q) := rfl

private theorem cochain_tensor_obj
    {C : Type*} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    (P Q : CochainComplex C ℤ) :
    P ⊗ Q = HomologicalComplex.mapBifunctor P Q (curriedTensor C) (.up ℤ) := rfl

private theorem Qh_quotient_obj
    {C : Type*} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    (P : CochainComplex C ℤ) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
      DerivedCategory.Q.obj P := rfl

private theorem Qh_quotient_map
    {C : Type*} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) =
      DerivedCategory.Q.map f := rfl

private theorem mapH_quotient
    {C D : Type*} [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (P : CochainComplex C ℤ) :
    (F.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
      (HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P) := rfl

end QuotientIdentities

namespace AlgebraicGeometry.ProEtale
open AlgebraicGeometry Scheme
namespace MixedRepForward
variable {A : Type (u + 1)} [CommRing A] [Finite A]
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
local notation "ShX" => Sheaf (Scheme.ProEt.topology X) (ModuleCat A)
local notation "ShU" => Sheaf (Scheme.ProEt.topology U) (ModuleCat A)
local notation "pull" => (j)^*[ModuleCat A]

/-- The published comparison satisfies its forward counit square on arbitrary complexes.

Proof. Apply `leftDerivedUpperStarTensorComparison_app_app_fac` to the homotopy
quotients of `P` and `Q`. Expand the two counits and combine their whiskered components
into a tensor of morphisms. The cochain tensorators equal the homotopy tensorators by
`cochainLocalization_tensorator_eq`; the homotopy oplax comparison is the quotient of
the signed-total cochain comparison. Finally `leftDerivedFactors_eq_counit` identifies
each pullback counit with its exact-derived factors. No tensorator is inverted.
(blueprint: lem-sf-finite-open-mixed-tensor-representative-forward-transport) -/
theorem forward_transport
    (P Q : CochainComplex ShX ℤ) :
    ((AlgebraicGeometry.ProEtale.leftDerivedUpperStarTensorNatIso
      (ModuleCat A) j).hom.app
      ((DerivedCategory.Q (C := ShX)).obj P)).app
      ((DerivedCategory.Q (C := ShX)).obj Q) ≫
      ((pull).leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.Q (C := ShX)).obj P) ≫
        (pull).mapDerivedCategoryFactors.hom.app P ⊗ₘ
       (pull).leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.Q (C := ShX)).obj Q) ≫
        (pull).mapDerivedCategoryFactors.hom.app Q) ≫
      (Functor.LaxMonoidal.μ (DerivedCategory.Q
        (C := ShU))
        (((pull).mapHomologicalComplex (.up ℤ)).obj P)
        (((pull).mapHomologicalComplex (.up ℤ)).obj Q)) =
      L(pull).map
        (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := ShX)) P Q) ≫
      ((pull).leftDerivedFunctorIsoMapDerivedCategory.hom.app
        ((DerivedCategory.Q (C := ShX)).obj
          (HomologicalComplex.mapBifunctor P Q
            (curriedTensor ShX) (.up ℤ))) ≫
        (pull).mapDerivedCategoryFactors.hom.app
          (HomologicalComplex.mapBifunctor P Q
            (curriedTensor ShX) (.up ℤ))) ≫
      (DerivedCategory.Q (C := ShU)).map
        (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
          pull).app P).app Q) := by
  exact forward_transport_general (ModuleCat.{u + 1} A) j P Q

end MixedRepForward
end AlgebraicGeometry.ProEtale
