/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.TensorBaseChange.ChangeOfRings
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.TensorBaseChange.Field

/-!
# The base change map for a flat sheaf and a sheaf

Let `K` be a field, `Λ` a finite ring whose exponent is invertible in `K`, and
`X' = X ×_K S'`, `Y = X' ×_{S'} T` with `g : T ⟶ S'` quasi-compact quasi-separated. For a flat
sheaf `E` of `Λ`-modules on `X` and a sheaf `F` on `T`, the base change map
`Lp^* E ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Lp^* E ⊗ᴸ Le^* F)` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_single`).

This is the single-sheaf case of blueprint `lem-kun-0f1j`. Since `Λ` is Artinian, `F` has a
finite filtration whose graded pieces are killed by maximal ideals `𝔪` of `Λ`, and the base
change map is a triangulated functor of `F`; for `F` killed by `𝔪` the change of rings
`Λ ⟶ Λ/𝔪` (`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_restrictScalars`) reduces to the
case of the finite field `Λ/𝔪` (`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_single_of_field`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The single-sheaf case of blueprint `lem-kun-0f1j`: for a flat sheaf `E` on `X` and a sheaf
`F` on `T`, the base change map `Lp^* E ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Lp^* E ⊗ᴸ Le^* F)` is an
isomorphism. -/
theorem isIso_tensorBaseChangeMap_single [Finite Λ] {K : Type u} [Field K]
    [HasInvertibleExponent Λ (Spec (.of K))] {X X' S' T Y : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) (b : S' ⟶ Spec (.of K)) (p : X' ⟶ X) (f' : X' ⟶ S')
    (_sq₁ : IsPullback p f' a b) (h : Y ⟶ X') (e : Y ⟶ T) (g : T ⟶ S') [QuasiCompact g]
    [QuasiSeparated g] (sq₂ : IsPullback h e f' g)
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (_hE : ObjectProperty.flat E)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g sq₂.w
      (L((p)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.singleFunctor _ 0).obj E))
      ((DerivedCategory.singleFunctor _ 0).obj F)) :=
  sorry

end Etale

end AlgebraicGeometry
