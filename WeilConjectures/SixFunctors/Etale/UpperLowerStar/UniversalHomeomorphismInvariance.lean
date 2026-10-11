/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.BaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Universal-homeomorphism invariance of the small étale topos

This file bundles the topological invariance results for a universal homeomorphism
`f : X ⟶ Y` into a single statement: base change along `f` is an equivalence of small étale
sites which preserves and reflects coverings, the pullback and pushforward functors on étale
sheaves are equivalences, and the comparison map on étale cohomology is bijective in every
degree.

## Main statements

- `AlgebraicGeometry.Etale.universalHomeomorphism_invariance`: the bundled statement.
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry.Etale

open Scheme

/-- **Universal-homeomorphism invariance**, [Stacks 03SI], [Stacks 04DZ]: let `f : X ⟶ Y` be a
universal homeomorphism. Then

* base change `V ↦ V ×_Y X` is an equivalence of the small étale sites of `Y` and `X`
  (`AlgebraicGeometry.Scheme.Hom.isEquivalence_etale`);
* a sieve is a covering if and only if its base change is
  (`AlgebraicGeometry.Scheme.Hom.functorPushforward_mem_smallEtaleTopology_iff`);
* the inverse image `f^*` and the direct image `f_*` are equivalences between the categories
  of `A`-valued étale sheaves on `Y` and on `X`, quasi-inverse to each other
  (`AlgebraicGeometry.Etale.isEquivalence_upperStar`,
  `AlgebraicGeometry.Etale.isEquivalence_lowerStar`,
  `AlgebraicGeometry.Etale.upperStarIsoInverse`);
* the comparison map `H^n(Y_ét, F) → H^n(X_ét, f^* F)` is bijective for every abelian étale
  sheaf `F` and every `n` (`AlgebraicGeometry.Etale.cohomologyMap_bijective`);
* every base change of `f` is again a universal homeomorphism
  (`AlgebraicGeometry.IsUniversalHomeomorphism.of_isPullback`), so all of the above applies to
  base changes of `f` as well.

(blueprint: `thm-weil-pbc-universal-homeomorphism-invariance`) -/
@[stacks 03SI]
theorem universalHomeomorphism_invariance (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsUniversalHomeomorphism f] :
    f.Etale.IsEquivalence ∧
      (∀ (U : Y.Etale) (S : Sieve U),
        S.functorPushforward f.Etale ∈ X.smallEtaleTopology (f.Etale.obj U) ↔
          S ∈ Y.smallEtaleTopology U) ∧
      ((f)^*[A]).IsEquivalence ∧ ((f)_*[A]).IsEquivalence ∧
      Nonempty ((f)^*[A] ≅ (sheafEquivalence A f).inverse) ∧
      (∀ (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ),
        Function.Bijective (cohomologyMap f F n)) ∧
      (∀ {X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X},
        IsPullback g' f' f g → IsUniversalHomeomorphism f') :=
  ⟨inferInstance, fun _ S ↦ f.functorPushforward_mem_smallEtaleTopology_iff S,
    isEquivalence_upperStar A f, isEquivalence_lowerStar A f, ⟨upperStarIsoInverse A f⟩,
    fun F n ↦ cohomologyMap_bijective f F n, fun sq ↦ IsUniversalHomeomorphism.of_isPullback sq⟩

end AlgebraicGeometry.Etale
