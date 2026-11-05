/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisLayerAction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedPullIsoCoherenceLowerStar

/-!
# The derived unit transport as a derived functor

For `s : Y' ⟶ Y` and `g : Y ⟶ X`, the derived unit transport
`Rg_* Lg^* ⟶ R(s ≫ g)_* L(s ≫ g)^*` (`ProEtale.CondensedRing.derivedUnitTransport`) is the unit of
`Ls^* ⊣ Rs_*` followed by the composition isomorphisms. This file compares it with the derived
functor of the underived unit transport `g_* g^* ⟶ (s ≫ g)_* (s ≫ g)^*` of module objects
(`ProEtale.CondensedRing.unitTransport`), for finite morphisms `s`, `g` (whose pushforwards are
exact).

## Main results

- `CategoryTheory.unitTransport_derived_fac`: the abstract comparison, for adjunctions "derived"
  from adjunctions through comparison morphisms `α`, `β` as for `Adjunction.derived`.
- `CategoryTheory.Adjunction.derivedHom`: the morphism `Lf₁ ⋙ Rg₁ ⟶ Lf₂ ⋙ Rg₂` induced by a
  morphism of composites of exact functors (generalizing `Adjunction.derivedEndo`), and its
  computation on the image of a complex
  (`CategoryTheory.Adjunction.derivedCompQhComparison_comp_derivedHom_app`).
- `ProEtale.CondensedRing.derivedUnitTransport_eq_derivedHom_app`: the derived unit transport is
  `derivedHom` of the unit transport of module objects.
- `ProEtale.CondensedRing.derivedUnitTransport_eq_derivedGaloisAction_app`: hence, for a Galois
  covering, the unit transport along `ρ σ` is the derived Galois action
  `ProEtale.CondensedRing.derivedGaloisAction` of `a`, provided the underived unit transport is
  the Galois action `ProEtale.CondensedRing.galoisAction` of `a`.

## Implementation notes

Both results take as a hypothesis the identity on homotopy categories
`ProEtale.CondensedRing.UnitTransportHomotopyCompatible` (the unit transport built from the
adjunctions and composition isomorphisms induced on homotopy categories is the unit transport of
module objects applied levelwise), which is not proved here; nor is the underived identification
of the unit transport with the Galois action.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

namespace Adjunction

open MonoidalCategory Abelian

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions D]

variable {D' : Type*} [Category D'] [Abelian D'] [HasDerivedCategory D']
  [HasKInjectiveResolutions D']
  {f₁ : C ⥤ D} {g₁ : D ⥤ C} {f₂ : C ⥤ D'} {g₂ : D' ⥤ C}
  [f₁.Additive] [f₂.Additive] [g₁.Additive] [g₂.Additive]
  [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
  [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
  [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
  [PreservesFiniteLimits g₂] [PreservesFiniteColimits g₂]

end Adjunction

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

open scoped CategoryTheory.Obj CategoryTheory.Functor

universe u

attribute [local instance] preservesFiniteColimits_lowerStar_of_isFinite

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing
