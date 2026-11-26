/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryIntegralPullbackConstruction
import WeilConjectures.WeilSheaf.Ordinary.OrdinaryCompletedIntegralPullback

/-! # The ordinary ringed pullback completion map

We construct the ordinary-to-completed pullback map in the ringed coordinates and show that
it is invertible on constructible inputs.
The comparison uses the canonical isomorphism of the two ordinary pullback models.

## Implementation details

The canonical adjunction identifies the ringed module pullback with the ordinary module
pullback, and exact localization is its total left derived functor, which gives `pullIso`.
The comparison is `pullIso` followed by `ordinaryIntegralCompletionComparison`, which is
invertible by `ordinaryCompletedIntegralPullback`.

## References

* [Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 6.5.9 and
  Proposition 6.6.11]
* [Stacks, Tag 03D2]
* [Stacks, Tag 06YY]
* [Stacks, Tag 08TC]
* [Stacks, Tag 0941]
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
namespace IntegralOrdinary
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Both direct coefficient maps are fixed by their finite quotient projections. -/
theorem directRing_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (sfCompletedCoefficientMap l E f) = ordinaryIntegralDirectRingMap l E f := by
  apply (ordinaryIntegralDirectRingMap_existsUnique l E f).unique
  · intro n
    exact congrArg ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map)
      ((sfCompletedCoefficientMap_existsUnique l E f).exists.choose_spec n)
  · exact (ordinaryIntegralDirectRingMap_existsUnique l E f).exists.choose_spec

/-- The canonical ordinary ringed and total-left-derived pullback models agree. -/
@[irreducible] def pullIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PurCompactSupport.pull (PurCompactSupport.completed l E) f ≅
      ordinaryIntegralDerivedPull l E f := by
  let R := PurCompactSupport.completed l E
  have hm : proEtaleRingDirectImageMap f (R.ring Y) (R.ring X) (R.pull f) =
      sfCompletedCoefficientMap l E f :=
    (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
      |>.apply_symm_apply (sfCompletedCoefficientMap l E f)
  let e : proEtaleRingModuleDirectImage f (R.ring Y) (R.ring X) (R.pull f) ≅
      ordinaryIntegralModulePush l E f := by
    unfold proEtaleRingModuleDirectImage ordinaryIntegralModulePush
    rw [hm]
    exact SheafOfModules.pushforwardCongr (directRing_eq l E f)
  let b := ((proEtaleRingModuleAdjunction f (R.ring Y) (R.ring X)
    (R.pull f)).ofNatIsoRight e).leftAdjointUniq (ordinaryIntegralModuleAdjunction l E f)
  have := preservesFiniteLimits_of_natIso b
  have := (ordinaryIntegralModuleAdjunction l E f).leftAdjoint_preservesColimits
  have := ordinaryIntegralModulePull_additive l E f
  let F := ordinaryIntegralModulePull l E f
  let W := HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ)
  let : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W F.mapDerivedCategory F.mapDerivedCategoryFactorsh
  let ε := ordinaryIntegralPullCounit l E f
  let : (ordinaryIntegralDerivedPull l E f).IsLeftDerivedFunctor ε W := by
    dsimp only [ε, ordinaryIntegralPullCounit, ordinaryIntegralDerivedPull]
    infer_instance
  let c : F.mapDerivedCategory ≅ ordinaryIntegralDerivedPull l E f :=
    Functor.leftDerivedUnique (ordinaryIntegralDerivedPull l E f) F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh.hom ε W
  exact Functor.mapDerivedCategoryNatIso b ≪≫ c

/-- The actual ordinary-to-completed pullback map in the ringed coordinates. -/
@[irreducible] def pullComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PurCompactSupport.pull (PurCompactSupport.completed l E) f ⟶
      integralDerivedPullback l E f :=
  (pullIso l E f).hom ≫ ordinaryIntegralCompletionComparison l E f

/-- The ringed-coordinate completion map is invertible on constructible inputs. -/
theorem pullComparison_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y]
    (hXdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (hYdim : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
    (hXinv : IsUnit (l : Γ(X, ⊤))) (hYinv : IsUnit (l : Γ(Y, ⊤)))
    (K : sfIntegralConstructibleCategory l E Y) :
    IsIso ((pullComparison l E f).app K.obj) := by
  have := (ordinaryCompletedIntegralPullback l E f hXdim hYdim hXinv hYinv
    K.obj K.property).2
  unfold pullComparison
  dsimp only [NatTrans.comp_app]
  infer_instance

end IntegralOrdinary
end WeilConjectures
