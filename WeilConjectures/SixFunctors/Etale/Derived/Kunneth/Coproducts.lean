/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FiniteCohomologicalDimension
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.LiftToFinset
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit

/-!
# Direct sums and finite cohomological dimension

For a quasi-compact quasi-separated morphism `f` of finite cohomological dimension, the derived
pushforward `Rf_*` on unbounded derived categories of étale sheaves of `Λ`-modules commutes with
direct sums, and similarly for `RΓ(X, -)` (blueprint `lem-kun-0f11`, Stacks 0F11).

The proof follows the blueprint. The higher direct images `R^q f_*` of sheaves commute with
filtered colimits (`AlgebraicGeometry.Etale.preservesFilteredColimitsOfSize_higherDirectImage`),
hence with direct sums, which are filtered colimits of finite direct sums. Then the unbounded
statement follows from the finiteness of the cohomological dimension: the coproduct of
K-injective complexes with injective components is a complex of `f_*`-acyclic objects, which
computes `Rf_*` (`CategoryTheory.Functor.preservesColimitsOfShape_rightDerivedFunctor`); this
replaces the hypercohomology spectral sequence of the blueprint.

## Main statements

- `AlgebraicGeometry.Etale.preservesCoproducts_rightDerivedLowerStar` and
  `AlgebraicGeometry.Etale.preservesCoproducts_rightDerivedGlobalSections` (`lem-kun-0f11`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The higher direct images `R^q f_*` along a quasi-compact quasi-separated morphism commute
with direct sums of étale sheaves of `Λ`-modules: direct sums are filtered colimits of finite
direct sums. -/
instance preservesColimitsOfShape_rightDerived_lowerStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (ι : Type (u + 1)) (q : ℕ) :
    PreservesColimitsOfShape (Discrete ι) (((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q) :=
  have := Etale.preservesFilteredColimitsOfSize_higherDirectImage Λ f q
  have : PreservesColimitsOfShape (Finset (Discrete ι))
      (((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q) :=
    preservesColimitsOfShape_of_natIso
      (((f)_*[ModuleCat.{u + 1} Λ]).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
        q)
  preservesColimitsOfShape_discrete_of_preservesColimitsOfShape_finset ι _

/-- Blueprint `lem-kun-0f11`: direct sums and finite cohomological dimension.

For a quasi-compact quasi-separated morphism `f` of finite cohomological dimension,
`Rf_* : D(X_ét, Λ) ⥤ D(Y_ét, Λ)` commutes with direct sums. -/
theorem preservesCoproducts_rightDerivedLowerStar {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hf : HasFiniteCohomologicalDimensionMorphism Λ f) (ι : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete ι) (R((f)_*[ModuleCat.{u + 1} Λ])) := by
  obtain ⟨d, hd⟩ := hf
  exact ((f)_*[ModuleCat.{u + 1} Λ]).preservesColimitsOfShape_rightDerivedFunctor_of_rightDerived
    ι d.toNat (fun F q hq ↦ Functor.isZero_rightDerived_of_isZero_homology _ F q (hd F q (by lia)))
    fun n ↦ inferInstance

/-- Blueprint `lem-kun-0f11`, part (2): for a quasi-compact quasi-separated scheme `X` of finite
cohomological dimension and a torsion ring `Λ`, `RΓ(X, -)` commutes with direct sums. -/
theorem preservesCoproducts_rightDerivedGlobalSections (hΛ : IsAddTorsion Λ) (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (hX : HasFiniteCohomologicalDimension Λ X)
    (ι : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete ι) (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X) :=
  sorry

end Etale

end AlgebraicGeometry
