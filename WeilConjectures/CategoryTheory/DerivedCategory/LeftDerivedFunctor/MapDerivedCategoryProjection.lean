/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatDevissage
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeGE
public import WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Devissage

/-!
# The projection map of the right adjoint of the functor induced by an exact monoidal functor

Let `F : C ⥤ D` be an exact strong monoidal functor between monoidal Grothendieck abelian
categories with functorial flat resolutions, which preserves flat objects and is a left adjoint,
and let `adj : D(F) ⊣ G` be an adjunction, where `D(F)` is the functor induced by `F` on derived
categories. For `E` in `D(D)` the projection map
`τ_E : G E ⊗ᴸ K ⟶ G (E ⊗ᴸ D(F) K)` (`CategoryTheory.Functor.mapDerivedCategoryProjectionMap`)
is the transpose of the comparison `D(F)(G E ⊗ᴸ K) ⟶ D(F) G E ⊗ᴸ D(F) K` followed by the
counit of `adj`. We show:

- `CategoryTheory.Functor.isIso_mapDerivedCategoryProjectionMap_app_tensorUnit`: `τ_E` is an
  isomorphism at the unit;
- `CategoryTheory.Functor.commShift_mapDerivedCategoryProjectionMap`: `τ_E` commutes with the
  shifts, for the commutation of `G` with the shifts induced by the adjunction;
- `CategoryTheory.Functor.isIso_mapDerivedCategoryProjectionMap_app_of_torAmplitudeGE`: if `G`
  does not lower the cohomological degree, `E` is bounded below and `τ_E` is an isomorphism at
  the flat objects placed in degree `0`, then `τ_E` is an isomorphism at every `K` of Tor
  amplitude in `[b, ∞)`. Such a `K` is represented by a K-flat complex `P` of flat objects
  vanishing below `b` whose image under `F` is K-flat; in a fixed degree `q`, both sides only
  depend on the stupid truncation `σ^{≤ N} P` for `N ≫ q`, which is a bounded complex of flat
  objects.
-/

@[expose] public section

universe u u₁ u₂

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory Pretriangulated

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

variable {F} {G : DerivedCategory D ⥤ DerivedCategory C} (adj : F.mapDerivedCategory ⊣ G)

end CategoryTheory.Functor
