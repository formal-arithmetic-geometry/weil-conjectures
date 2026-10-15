/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
import Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import Sheaf.AlgebraicGeometry.ModuleAbelianInverseImageComparison
import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
# Exchange and forgetting coefficients

Source: literature/stacks-project/sites-cohomology.tex, Tags 0D6J and 07A7
(blueprint: lem-weil-pbc-exchange-forget-coefficients).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Forgetting the coefficient ring identifies the derived exchange morphism.

Source: Stacks Project, sites-cohomology.tex, Lemma 0D6J(3) and Remark 07A7;
etale-cohomology.tex, Lemma 03Q1(1).
(blueprint: lem-weil-pbc-exchange-forget-coefficients)

Proof:
1. Kernels are the same subsheaves and cokernels are sheafifications of the same
quotients after forgetting scalars. Thus `moduleAbelianForget` is exact, preserves
cohomology and quasi-isomorphisms, and descends termwise to the bounded below
localization. The cohomology identification is the natural isomorphism of the
existing `Functor.mapDerivedCategoryPlusHomologyFunctorIso`.
2. Use `lem-weil-pbc-etale-constant-ring-module-equivalence` to identify module-valued
sheaves with modules over the constant ring sheaf. The equivalence retains underlying
abelian sheaves and is exact in both directions by the universal properties of
kernels and cokernels. It therefore transports injectives, derived direct images,
and inverse-image adjunctions, including their units, counits and square comparisons.
3. By `lem-weil-pbc-module-abelian-inverse-image-comparison`, the abelian adjoint of
the forgotten module unit is invertible. Naturality of the unit and adjunction gives
the canonical inverse-image comparison on each of the four edges.
4. Apply `lem-weil-pbc-module-abelian-derived-direct-image-comparison` to `f` and `f'`.
These are the unit-compatible natural comparisons. In the K-injective model of
0D6J(3), they are represented by direct image of a module resolution followed by
an abelian K-injective replacement; exactness alone does not identify the resolutions.
5. Apply `lem-weil-pbc-module-abelian-derived-exchange-compatibility` to `sq.toCommSq`.
Its source and target isomorphisms use precisely the preceding canonical comparisons.
The resulting equation identifies the forgotten adjoint mate with the abelian mate.
6. Forgetting reflects isomorphisms of module sheaves: the inverse of an invertible
underlying additive map is linear by injectivity of the original map. The cohomology
comparison and `lem-weil-pbc-derived-plus-iso-on-cohomology` then show reflection on
derived categories. Every functor preserves isomorphisms; combine this with step 5
and invertibility of both endpoint comparisons to obtain the concluding equivalence.
-/
theorem exchange_forget_coefficients
    (Λ : Type (u + 1)) [CommRing Λ]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (∀ (T : Scheme.{u}) (i : ℤ),
      Nonempty
        (D+(moduleAbelianForget Λ T) ⋙
            DerivedCategory.Plus.homologyFunctor
              (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) i ≅
          DerivedCategory.Plus.homologyFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) i ⋙
            moduleAbelianForget Λ T)) ∧
    (∀ (T : Scheme.{u}),
      PreservesFiniteLimits (moduleAbelianForget Λ T) ∧
      PreservesFiniteColimits (moduleAbelianForget Λ T)) ∧
      IsIso (moduleAbelianUpperStarComparison Λ f) ∧
      IsIso (moduleAbelianUpperStarComparison Λ f') ∧
      IsIso (moduleAbelianUpperStarComparison Λ g) ∧
      IsIso (moduleAbelianUpperStarComparison Λ g') ∧
      IsIso (moduleAbelianDerivedLowerStarComparison Λ f) ∧
      IsIso (moduleAbelianDerivedLowerStarComparison Λ f') ∧
      (D+(moduleAbelianForget Λ Y').map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) ≫
        (moduleAbelianDerivedExchangeTargetIso Λ g' f' K).hom =
      (moduleAbelianDerivedExchangeSourceIso Λ f g K).hom ≫
        (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
          (D+(moduleAbelianForget Λ X).obj K)) ∧
      (IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) ↔
        IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
          (D+(moduleAbelianForget Λ X).obj K))) := by
  sorry

end AlgebraicGeometry.Etale
