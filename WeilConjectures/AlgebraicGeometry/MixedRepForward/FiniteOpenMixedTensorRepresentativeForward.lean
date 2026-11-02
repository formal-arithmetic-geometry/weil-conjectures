/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMon.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.MixedRepForward.ForwardTransportGeneral
public import WeilConjectures.AlgebraicGeometry.MixedRepForward.FiniteCoefficientInstances

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
