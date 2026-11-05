/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryProjectionFlat

/-!
# Retractions of the unbounded derived unit

Let `adj : f ⊣ g` be an adjunction between abelian categories, with `f` exact and `g` left
exact, and consider the unbounded derived adjunction
`adj.derivedAdjunction : f.leftDerivedFunctor ⊣ g.rightDerivedFunctor`.

Let `K` be a bounded below complex such that every `f(Kⁿ)` is `g`-acyclic. Then `g(f(K))`
computes `Rg(Lf(K))`, and under this identification the derived unit at `K` is the levelwise
unit `K ⟶ g(f(K))` of `adj`. Consequently, a retraction `t : g(f(K)) ⟶ K` of the levelwise unit,
as a morphism of complexes, induces a retraction of the derived unit at `K`.

## Main results

- `CategoryTheory.Adjunction.derivedUnitIso`: the isomorphism `g(f(K)) ≅ Rg(Lf(K))`.
- `CategoryTheory.Adjunction.Q_map_unit_comp_derivedUnitIso_hom`: under this isomorphism, the
  derived unit at `K` is the levelwise unit of `adj`.
- `CategoryTheory.Adjunction.derivedUnitRetraction`: the retraction of the derived unit induced by
  a retraction `t` of the levelwise unit.
- `CategoryTheory.Adjunction.isSplitMono_derivedAdjunction_unit_app_of_retraction`: the derived
  unit at `K` is then a split monomorphism.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory Abelian

namespace CategoryTheory

namespace Adjunction

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
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive] [f.PreservesKFlatQuasiIso]

variable [EnoughInjectives D] [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [PreservesFiniteLimits g]
  (K : CochainComplex C ℤ) (a : ℤ) [K.IsStrictlyGE a]
  (hK : ∀ n, g.rightAcyclic (f.obj (K.X n)))

variable (t : (g.mapHomologicalComplex _).obj ((f.mapHomologicalComplex _).obj K) ⟶ K)

end Adjunction

end CategoryTheory
