/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# Cohomological dimension of étale sheaves of `Λ`-modules

The (torsion étale) cohomological dimension of a scheme and of a morphism, for sheaves of
`Λ`-modules (blueprint `def-kun-cd`), and its finiteness for schemes and morphisms of finite type
over a field (blueprint `lem-kun-0f10`, Stacks 0F10).

## Main definitions and statements

- `AlgebraicGeometry.Etale.HasFiniteCohomologicalDimension`,
  `AlgebraicGeometry.Etale.HasFiniteCohomologicalDimensionMorphism` (`def-kun-cd`).
- `AlgebraicGeometry.Etale.hasFiniteCohomologicalDimensionMorphism` and
  `AlgebraicGeometry.Etale.hasFiniteCohomologicalDimension_of_isSepClosed` (`lem-kun-0f10`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Defs

variable (X : Scheme.{u})

/-- Blueprint `def-kun-cd` (for sheaves of `Λ`-modules): the scheme `X` has *finite
cohomological dimension* for sheaves of `Λ`-modules if there is a `d` with `H^q(X, F) = 0` for
every étale sheaf `F` of `Λ`-modules and every `q > d`. For a torsion ring `Λ` every such sheaf
is a torsion abelian sheaf, so this follows from finiteness of the torsion étale cohomological
dimension `cd(X)` of the blueprint. -/
def HasFiniteCohomologicalDimension : Prop :=
  ∃ d : ℤ, ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), d < q →
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) X q).obj
      ((DerivedCategory.singleFunctor _ 0).obj F))

variable {X} in
/-- Blueprint `def-kun-cd` (for morphisms, and sheaves of `Λ`-modules): the morphism `f` has
*finite cohomological dimension* for sheaves of `Λ`-modules if there is a `d` with
`R^q f_* F = 0` for every étale sheaf `F` of `Λ`-modules and every `q > d`. -/
def HasFiniteCohomologicalDimensionMorphism {Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ d : ℤ, ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), d < q →
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj F)))

end Defs

/-- Blueprint `lem-kun-0f10`: finite cohomological dimension of finite-type morphisms, part (1).

Let `K` be a field and `f : X ⟶ Y` a morphism between `K`-schemes of finite type. For a torsion
coefficient ring `Λ`, the higher direct images `R^q f_*` of étale sheaves of `Λ`-modules vanish
in all large degrees `q`. -/
theorem hasFiniteCohomologicalDimensionMorphism (hΛ : IsAddTorsion Λ) {K : Type u} [Field K]
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (_hf : f ≫ aY = aX) :
    HasFiniteCohomologicalDimensionMorphism Λ f :=
  sorry

/-- Blueprint `lem-kun-0f10`: finite cohomological dimension of finite-type morphisms, part (2).

Over a separably closed field `K`, a `K`-scheme `X` of finite type has finite étale
cohomological dimension: for a torsion coefficient ring `Λ`, `H^q(X, F) = 0` for every étale
sheaf `F` of `Λ`-modules and all large `q`. -/
theorem hasFiniteCohomologicalDimension_of_isSepClosed (hΛ : IsAddTorsion Λ) {K : Type u}
    [Field K] [IsSepClosed K] {X : Scheme.{u}} (aX : X ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] :
    HasFiniteCohomologicalDimension Λ X :=
  sorry

end Etale

end AlgebraicGeometry
