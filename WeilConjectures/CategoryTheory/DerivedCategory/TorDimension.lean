/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.Over
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-!
# Tor dimension

Let `(C, J)` be a site and `R` a commutative ring, and write `D(J, R)` for the derived
category of sheaves of `R`-modules on `(C, J)`, i.e. of modules over the constant sheaf of
rings `R`. Following [Stacks 08FY] we define, for an object `E` of `D(J, R)` and integers
`a ≤ b`:

1. `E` has *tor-amplitude in `[a, b]`* (`DerivedCategory.torAmplitudeIn`) if
   `Hⁱ(E ⊗ᴸ F) = 0` for all sheaves of `R`-modules `F` and all `i ∉ [a, b]`;
2. `E` has *finite tor dimension* (`DerivedCategory.finiteTorDimension`) if it has
   tor-amplitude in `[a, b]` for some `a ≤ b`;
3. `E` *locally has finite tor dimension* (`DerivedCategory.locallyFiniteTorDimension`) if
   for every object `U` of `C` there is a covering `{Uᵢ ⟶ U}` such that each restriction
   `E|_{Uᵢ}` has finite tor dimension.

The derived tensor product `E ⊗ᴸ F` is the tensor product of the monoidal structure on
`D(J, R)` of `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`,
applied to `E` and the sheaf `F` placed in degree `0`. A covering `{Uᵢ ⟶ U}` is a presieve
on `U` generating a covering sieve. The restriction `E|_V` to an object `V` of `C` lives in
the derived category of sheaves on the localized site `J.over V`, and is induced by the
exact restriction functor `J.overPullback` (`DerivedCategory.restrictOver`).

As in `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`, the site has objects in
`Type (u + 1)`, `Hom`-types in `Type u` and is essentially small in `u + 1`, and the ring
lives in `Type (u + 1)`; the localized sites `J.over V` are then of the same shape.

## Exactness of the restriction

The restriction `J.overPullback (ModuleCat R) V` along the continuous and cocontinuous
`Over.forget V` is a right adjoint (to the pullback), hence left exact, and a left adjoint
(`Functor.sheafAdjunctionCocontinuous`, to the pushforward along the cocontinuous
`Over.forget V`), hence right exact. The right Kan extensions along `(Over.forget V).op`
entering the second adjunction exist because `ModuleCat.{u + 1} R` has limits indexed by
categories with objects in `Type (u + 1)` and morphisms in `Type u`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) (R : Type (u + 1)) [CommRing R]

namespace CategoryTheory.GrothendieckTopology

/-- The pointwise right Kan extensions along `(Over.forget V).op` of presheaves of
`R`-modules exist: `ModuleCat.{u + 1} R` has the limits needed. -/
instance hasPointwiseRightKanExtension_op_overForget (V : C)
    (P : (Over V)ᵒᵖ ⥤ ModuleCat.{u + 1} R) :
    (Over.forget V).op.HasPointwiseRightKanExtension P := by
  have : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} R) :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  infer_instance

/-- The restriction of sheaves of `R`-modules to the localized site `J.over V` is a left
adjoint, to the pushforward along the cocontinuous functor `Over.forget V`. -/
instance isLeftAdjoint_overPullback (V : C) :
    (J.overPullback (ModuleCat.{u + 1} R) V).IsLeftAdjoint :=
  ((Over.forget V).sheafAdjunctionCocontinuous (ModuleCat.{u + 1} R) (J.over V) J).isLeftAdjoint

/-- The restriction of sheaves of `R`-modules to the localized site `J.over V` is
additive. -/
instance additive_overPullback (V : C) : (J.overPullback (ModuleCat.{u + 1} R) V).Additive :=
  Functor.additive_of_preserves_binary_products _

end CategoryTheory.GrothendieckTopology

namespace DerivedCategory

/-- The restriction `E ↦ E|_V` from `D(J, R)` to the derived category of sheaves of
`R`-modules on the localized site `J.over V`: the functor induced by the exact restriction
functor `J.overPullback`. -/
noncomputable def restrictOver (V : C) :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf (J.over V) (ModuleCat.{u + 1} R)) :=
  (J.overPullback (ModuleCat.{u + 1} R) V).mapDerivedCategory

/-- An object `E` of `D(J, R)` has *tor-amplitude in `[a, b]`* [Stacks 08FY] if
`Hⁱ(E ⊗ᴸ F) = 0` for all sheaves of `R`-modules `F` and all `i ∉ [a, b]`. -/
noncomputable def torAmplitudeIn (a b : ℤ) :
    ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  fun E ↦ ∀ (F : Sheaf J (ModuleCat.{u + 1} R)) (i : ℤ), i ∉ Set.Icc a b →
    IsZero ((homologyFunctor _ i).obj (E ⊗ (singleFunctor _ 0).obj F))

/-- An object `E` of `D(J, R)` has *finite tor dimension* [Stacks 08FY] if it has
tor-amplitude in `[a, b]` for some integers `a ≤ b`. -/
noncomputable def finiteTorDimension :
    ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  fun E ↦ ∃ a b : ℤ, a ≤ b ∧ torAmplitudeIn J R a b E

/-- An object `E` of `D(J, R)` *locally has finite tor dimension* [Stacks 08FY] if for every
object `U` of `C` there is a covering `{Uᵢ ⟶ U}` — a presieve on `U` generating a covering
sieve — such that each restriction `E|_{Uᵢ}` has finite tor dimension. -/
noncomputable def locallyFiniteTorDimension :
    ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  fun E ↦ ∀ U : C, ∃ S : Presieve U, Sieve.generate S ∈ J U ∧
    ∀ ⦃V : C⦄ (f : V ⟶ U), S f → finiteTorDimension (J.over V) R ((restrictOver J R V).obj E)

end DerivedCategory
