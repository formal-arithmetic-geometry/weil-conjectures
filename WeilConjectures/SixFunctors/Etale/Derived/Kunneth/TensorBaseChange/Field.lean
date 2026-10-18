/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.FilteredColimit
public import WeilConjectures.ConstructibleSheaf.FinitePushforward
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.TensorBaseChange.FinitePushforward
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.TensorBaseChange.Restriction
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.TensorBaseChange.Unit
public import WeilConjectures.SixFunctors.Etale.FieldBaseChange.Derived

/-!
# The base change map for single sheaves over a finite field of coefficients

Let `K` be a field, `k` a finite field whose characteristic is invertible in `K`, and
`X' = X ×_K S'`, `Y = X' ×_{S'} T` with `g : T ⟶ S'` quasi-compact quasi-separated. For all
sheaves `E` of `k`-vector spaces on `X` and `F` on `T`, the base change map
`Lp^* E ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Lp^* E ⊗ᴸ Le^* F)` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_single_of_field`).

This is "the `𝔽_ℓ`-vector space case" of the proof of blueprint `lem-kun-0f1j`: the question is
local on `X` (`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_of_affineOpens`); on an affine
`X`, `E` is a filtered colimit of constructible sheaves (`lem-kun-03sa`), a constructible sheaf
embeds into a finite sum of pushforwards `π_* k` along finite morphisms
(`AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar`) with constructible cokernel, and for
`π_* k` the base change map is identified with the base change of `Rg_*` along
`X_i ×_K S' ⟶ S'` (`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_rightDerivedLowerStar_of_isFinite`,
`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_unit_iff`), an isomorphism by
`lem-kun-0f1i` (`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_field`). Since `k` is a
field, all tensor products are exact, and the dimension-shifting argument on the cohomology
sheaves concludes.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (k : Type (u + 1)) [Field k] [Finite k]

/-- The `𝔽_ℓ`-vector space case of blueprint `lem-kun-0f1j`: over a finite field of coefficients
whose characteristic is invertible in `K`, the base change map
`Lp^* E ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Lp^* E ⊗ᴸ Le^* F)` is an isomorphism for all sheaves `E` on
`X` and `F` on `T`. -/
theorem isIso_tensorBaseChangeMap_single_of_field {K : Type u} [Field K]
    [HasInvertibleExponent k (Spec (.of K))] {X X' S' T Y : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K)) (p : X' ⟶ X) (f' : X' ⟶ S')
    (_sq₁ : IsPullback p f' a b) (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [QuasiCompact g]
    [QuasiSeparated g] (sq₂ : IsPullback h e f' g)
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k))
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} k)) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} k) h e f' g sq₂.w
      (L((p)^*[ModuleCat.{u + 1} k]).obj ((DerivedCategory.singleFunctor _ 0).obj E))
      ((DerivedCategory.singleFunctor _ 0).obj F)) :=
  sorry

end Etale

end AlgebraicGeometry
