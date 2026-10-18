/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.TensorBaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar

/-!
# Change of coefficient rings in the base change map

Let `φ : Λ ⟶ Λ'` be a surjective morphism of commutative rings, `E` a flat sheaf of
`Λ`-modules on `X` and `N` a sheaf of `Λ'`-modules on `T`. Since `E` is flat,
`Lp^* E ⊗ᴸ_Λ M ≅ Lp^*(Λ' ⊗_Λ E) ⊗ᴸ_{Λ'} M` for every complex `M` of `Λ'`-modules (viewed as
`Λ`-modules), and restriction of scalars commutes with the pullbacks and the derived
pushforwards. Under these identifications the base change map over `Λ` at `(E, N)` is the
restriction of scalars of the base change map over `Λ'` at `(Λ' ⊗_Λ E, N)`; in particular it is
an isomorphism if the latter is
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_restrictScalars`).

This is the change of rings `lem-kun-change-of-rings-tensor` in the reduction to `𝔽_ℓ`-coefficients
of the proof of blueprint `lem-kun-0f1j`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

variable {X X' S' T Y : Scheme.{u}}

/-- The base change map over `Λ` at a flat sheaf `E` and the restriction of scalars of a sheaf
`N` of `Λ'`-modules is an isomorphism if the base change map over `Λ'` at the extension of
scalars `Λ' ⊗_Λ E` and `N` is. -/
theorem isIso_tensorBaseChangeMap_restrictScalars (hφ : Function.Surjective φ)
    (p : X' ⟶ X) (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S') (w : h ≫ f' = e ≫ g)
    (E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (_hE : ObjectProperty.flat E)
    (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
    (_H : IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ') h e f' g w
      (L((p)^*[ModuleCat.{u + 1} Λ']).obj ((DerivedCategory.singleFunctor _ 0).obj
        ((Sheaf.composeAndSheafify X.smallEtaleTopology
          (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)).obj E)))
      ((DerivedCategory.singleFunctor _ 0).obj N))) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g w
      (L((p)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.singleFunctor _ 0).obj E))
      ((DerivedCategory.singleFunctor _ 0).obj
        ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj N))) :=
  sorry

end Etale

end AlgebraicGeometry
